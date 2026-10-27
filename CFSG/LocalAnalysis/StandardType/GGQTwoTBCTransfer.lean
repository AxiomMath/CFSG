module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

private theorem ggFix_conj_eq_centralizer_aux {X : Type*} [Group X] (d : X) :
    ggFix (MulAut.conj d) = Subgroup.centralizer ({d} : Set X) := by
  ext x
  rw [mem_ggFix, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

private theorem isComponentOf_map_centralizer_of_central_cover_aux
    {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) (d : X) {J : Subgroup X}
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({d} : Set X))) :
    CFSG.Assembly.IsComponentOf (J.map f) (Subgroup.centralizer ({f d} : Set Y)) := by
  have hJ' : CFSG.Assembly.IsComponentOf J (ggFix (MulAut.conj d)) := by
    rwa [ggFix_conj_eq_centralizer_aux d]
  have h := LayerCC.isComponentOf_map_ggFix (β := MulAut.conj (f d)) hf hker
    (fun x => by simp [MulAut.conj_apply]) hJ'
  simpa only [ggFix_conj_eq_centralizer_aux (f d)] using h

private theorem ggIsReflection_congr_of_mulEquiv {p : ℕ} {G : Type} [Group G]
    {A : Subgroup G} {V : Type*} [Group V] (Θ : V ≃* ↥A) {s : MulAut V}
    (hs : s ^ 2 = 1) (hfix : Nat.card {f : V // s f = f} * p = Nat.card V) :
    GGIsReflection p (MulAut.congr Θ s) := by
  refine ⟨by rw [← map_pow, hs, map_one], ?_⟩
  have h1 : Nat.card {a : ↥A // MulAut.congr Θ s a = a} =
      Nat.card {f : V // s f = f} := by
    refine Nat.card_congr (Equiv.subtypeEquiv Θ.symm.toEquiv fun a => ?_)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.toEquiv_eq_coe,
      MulEquiv.coe_toEquiv]
    constructor
    · intro h
      have h' := congrArg Θ.symm h
      rwa [MulEquiv.symm_apply_apply] at h'
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
  rw [h1, hfix]
  exact Nat.card_congr Θ.toEquiv

private theorem eq_one_of_mem_ker_of_pow_three_eq_one {X Y : Type*} [Group X] [Group Y]
    [Finite X] {f : X →* Y} (h3 : ¬ 3 ∣ Nat.card f.ker) {z : X}
    (hz : z ∈ f.ker) (hz3 : z ^ 3 = 1) : z = 1 := by
  have hzcard3 : Nat.card (Subgroup.zpowers z) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hz3
  have hzcardK : Nat.card (Subgroup.zpowers z) ∣ Nat.card f.ker :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz)
  have h1 : Nat.card (Subgroup.zpowers z) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hzcard3 with h | h
    · exact h
    · exact absurd (h ▸ hzcardK) h3
  have hzbot : Subgroup.zpowers z = ⊥ := Subgroup.card_eq_one.mp h1
  have hzmem : z ∈ (⊥ : Subgroup X) := hzbot ▸ Subgroup.mem_zpowers z
  simpa using hzmem

private theorem mem_normalizer_map_aux {G H : Type*} [Group G] [Group H] (f : G →* H)
    {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    f g ∈ Subgroup.normalizer (K.map f : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g * x * g⁻¹, (hg x).1 hx, by simp only [map_mul, map_inv]⟩
  · rintro ⟨x, hx, hxeq⟩
    have hy : y = f (g⁻¹ * x * g) := by
      calc y = (f g)⁻¹ * (f g * y * (f g)⁻¹) * f g := by group
        _ = (f g)⁻¹ * f x * f g := by rw [← hxeq]
        _ = f (g⁻¹ * x * g) := by simp only [map_mul, map_inv]
    rw [hy]
    refine ⟨g⁻¹ * x * g, ?_, rfl⟩
    exact (hg (g⁻¹ * x * g)).2 (by
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group])


private theorem mem_ggAutomizer_map_of_mem {G₁ G₂ : Type} [Group G₁] [Group G₂]
    {f : G₁ →* G₂} {A B : Subgroup G₁} {B' : Subgroup G₂} (hB : B.map f = B')
    (e : ↥B ≃* ↥B') (he : ∀ b : ↥B, ((e b : ↥B') : G₂) = f b)
    {φ : MulAut ↥B} (hφ : φ ∈ ggAutomizer A B) :
    MulAut.congr e φ ∈ ggAutomizer (A.map f) B' := by
  obtain ⟨g, hgA, hgN, hgind⟩ := mem_ggAutomizer_iff.mp hφ
  have hgN' : f g ∈ Subgroup.normalizer (B' : Set G₂) := by
    rw [← hB]
    exact mem_normalizer_map_aux f hgN
  refine mem_ggAutomizer_iff.mpr ⟨f g, Subgroup.mem_map_of_mem f hgA, hgN', ?_⟩
  intro b'
  obtain ⟨b, rfl⟩ := e.surjective b'
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [he (φ b), he b, hgind b, map_mul, map_mul, map_inv]

private theorem map_subtype_centralizer_singleton_aux {G : Type*} [Group G]
    (C : Subgroup G) (b : C) :
    (Subgroup.centralizer ({b} : Set C)).map C.subtype =
      C ⊓ Subgroup.centralizer ({(b : G)} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
  · rintro ⟨hx, hxb⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxb, rfl⟩

private theorem mem_normalizer_subgroupOf_of_map_subtype {G : Type} [Group G]
    {L : Subgroup G} {H' : Subgroup ↥L} {g : ↥L}
    (hg : (g : G) ∈ Subgroup.normalizer (H'.map L.subtype : Set G)) :
    g ∈ Subgroup.normalizer (H' : Set ↥L) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    have hmap : L.subtype (g * x * g⁻¹) ∈ H'.map L.subtype := by
      have h1 := (hg (L.subtype x)).1 (Subgroup.mem_map_of_mem L.subtype hx)
      convert h1 using 2
      rfl
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).1 hmap
  · intro hx
    have h1 : L.subtype x ∈ H'.map L.subtype :=
      (hg (L.subtype x)).2 (by
        convert Subgroup.mem_map_of_mem L.subtype hx using 2
        rfl)
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).1 h1

private theorem mem_normalizer_of_map_mem_normalizer {X Y : Type*} [Group X] [Group Y]
    [Finite X] (f : X →* Y) (hker : f.ker ≤ Subgroup.center X)
    (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1 → z = 1) {H : Subgroup X}
    (hH3 : ∀ h ∈ H, h ^ 3 = 1) {g : X}
    (hg : f g ∈ Subgroup.normalizer (H.map f : Set Y)) :
    g ∈ Subgroup.normalizer (H : Set X) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨h, hh, rfl⟩
    have hmem : f (g * h * g⁻¹) ∈ H.map f := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hg) (f h) |>.1
        (Subgroup.mem_map_of_mem f hh)
      simpa only [map_mul, map_inv] using h1
    obtain ⟨h', hh', hfh'⟩ := hmem
    set a : X := g * h * g⁻¹ with ha
    set z : X := h'⁻¹ * a with hz
    have hzker : z ∈ f.ker := by
      rw [MonoidHom.mem_ker, hz]
      simp only [map_mul, map_inv, hfh', inv_mul_cancel]
    have hcz : Commute h' z :=
      Subgroup.mem_center_iff.mp (hker hzker) h'
    have haeq : a = h' * z := by
      rw [hz]
      group
    have hcomm : Commute h' a := by
      rw [haeq]
      exact (Commute.refl h').mul_right hcz
    have ha3 : a ^ 3 = 1 := by
      rw [ha, conj_pow, hH3 h hh]
      simp
    have hz3 : z ^ 3 = 1 := by
      rw [hz, hcomm.inv_left.mul_pow, ha3, mul_one, inv_pow, hH3 h' hh', inv_one]
    have hz1 : z = 1 := hker3 z hzker hz3
    change a ∈ H
    rw [haeq, hz1, mul_one]
    exact hh'
  have hcard : Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem ggTBCReflCore_of_surjective {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    {r : ℕ} (f : X →* Y) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X)
    (h3 : ¬ 3 ∣ Nat.card f.ker) (h : GGTBCReflCore Y r) : GGTBCReflCore X r := by
  intro H hHA hHcard d hdH hd1 J hJ φ hφmem hφrefl
  classical
  have hker3 : ∀ z ∈ f.ker, z ^ 3 = 1 → z = 1 :=
    fun z hz hz3 => eq_one_of_mem_ker_of_pow_three_eq_one h3 hz hz3
  have hinjH : Function.Injective (f.subgroupMap H) := by
    intro a b hab
    have hzmem : ((a : H)⁻¹ * (b : H) : X) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      change f ((a : X)⁻¹ * (b : X)) = 1
      rw [map_mul, map_inv, show f (a : X) = f (b : X) from congrArg Subtype.val hab,
        inv_mul_cancel]
    have hz3 : (((a : H)⁻¹ * (b : H) : H) : X) ^ 3 = 1 :=
      hHA.2 _ (H.mul_mem (H.inv_mem a.2) b.2)
    have hz1 : (((a : H)⁻¹ * (b : H) : H) : X) = 1 := hker3 _ hzmem hz3
    have hz1H : (a : H)⁻¹ * (b : H) = 1 := Subtype.ext hz1
    have hba : (b : H) = (a : H) := by
      have h := congrArg (fun x : H => (a : H) * x) hz1H
      simpa using h
    exact hba.symm
  let e : ↥H ≃* ↥(H.map f) :=
    MulEquiv.ofBijective (f.subgroupMap H) ⟨hinjH, f.subgroupMap_surjective H⟩
  have he : ∀ b : ↥H, ((e b : ↥(H.map f)) : Y) = f b := fun b => rfl
  let Hbar : Subgroup Y := H.map f
  let dbar : Y := f d
  have hdbar_mem : dbar ∈ Hbar := Subgroup.mem_map_of_mem f hdH
  have hdbar_ne : dbar ≠ 1 := by
    intro h1
    apply hd1
    have hd1H : (⟨d, hdH⟩ : ↥H) = 1 := by
      apply hinjH
      apply Subtype.ext
      simpa using h1
    exact congrArg Subtype.val hd1H
  have hHAbar : CFSG.Open.IsElemAbelian 3 Hbar := hHA.map f
  have hHcardbar : Nat.card Hbar = 3 ^ r := by
    rw [← hHcard]
    exact (Nat.card_congr e.toEquiv).symm
  have hJbar : CFSG.Assembly.IsComponentOf (J.map f) (Subgroup.centralizer ({dbar} : Set Y)) :=
    isComponentOf_map_centralizer_of_central_cover_aux f hf hker d hJ
  have hφbar_mem : MulAut.congr e φ ∈
      ggAutomizer (Subgroup.centralizer ({dbar} : Set Y)) Hbar := by
    obtain ⟨g, hgC, hgN, hgind⟩ := mem_ggAutomizer_iff.mp hφmem
    have hfgC : f g ∈ Subgroup.centralizer ({dbar} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hgC ⊢
      have h := congrArg f hgC
      simpa only [map_mul] using h
    have hfgN : f g ∈ Subgroup.normalizer (Hbar : Set Y) := mem_normalizer_map_aux f hgN
    refine mem_ggAutomizer_iff.mpr ⟨f g, hfgC, hfgN, ?_⟩
    intro b'
    obtain ⟨b, rfl⟩ := e.surjective b'
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [he (φ b), he b, hgind b, map_mul, map_mul, map_inv]
  have hφbar_refl : GGIsReflection 3 (MulAut.congr e φ) :=
    ggIsReflection_congr_of_mulEquiv (G := Y) (A := Hbar) e hφrefl.1 hφrefl.2
  have hres := h Hbar hHAbar hHcardbar dbar hdbar_mem hdbar_ne
    (J.map f) hJbar (MulAut.congr e φ) hφbar_mem hφbar_refl
  rcases hres with hmem | hcomm
  · left
    obtain ⟨g, hgJbar, hgN, hgind⟩ := mem_ggAutomizer_iff.mp hmem
    obtain ⟨j, hjJ, rfl⟩ := Subgroup.mem_map.mp hgJbar
    have hjN : j ∈ Subgroup.normalizer (H : Set X) :=
      mem_normalizer_of_map_mem_normalizer f hker hker3 hHA.2 hgN
    have hφj : ∀ b : ↥H, φ b = ggConjAut H hjN b := by
      intro b
      have hmemj : (j * (b : X) * j⁻¹) ∈ H :=
        (Subgroup.mem_normalizer_iff.mp hjN (b : X)).1 b.2
      have h1 := hgind (e b)
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
      rw [he (φ b), he b] at h1
      have h2 : f ((φ b : ↥H) : X) = f (j * (b : X) * j⁻¹) := by
        rw [h1]
        simp only [map_mul, map_inv]
      have hEqH : φ b = ⟨j * (b : X) * j⁻¹, hmemj⟩ :=
        hinjH (Subtype.ext h2)
      rw [hEqH]
      apply Subtype.ext
      rw [ggConjAut_apply]
    have hφeq : φ = ggConjAut H hjN := MulEquiv.ext hφj
    rw [hφeq]
    exact ggConjAut_mem_ggAutomizer hjJ hjN
  · right
    intro ψ hψmem
    obtain ⟨g, hgJ, hgN, hgind⟩ := mem_ggAutomizer_iff.mp hψmem
    have hψbar_mem : MulAut.congr e ψ ∈
        ggAutomizer (J.map f) Hbar := by
      refine mem_ggAutomizer_iff.mpr
        ⟨f g, Subgroup.mem_map_of_mem f hgJ, mem_normalizer_map_aux f hgN, ?_⟩
      intro b'
      obtain ⟨b, rfl⟩ := e.surjective b'
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [he (ψ b), he b, hgind b, map_mul, map_mul, map_inv]
    have hc := hcomm _ hψbar_mem
    have hc' : MulAut.congr e (φ * ψ) = MulAut.congr e (ψ * φ) := by
      rw [map_mul, map_mul]
      exact hc
    exact (MulAut.congr e).injective hc'


theorem ggTBCReflCoreIn_iff {G : Type} [Group G] [Finite G] {r : ℕ} (L : Subgroup G) :
    GGTBCReflCoreIn r L ↔ GGTBCReflCore ↥L r := by
  constructor
  · intro hIn H' hH'ea hH'card d' hd'H' hd'1 J' hJ' φ' hφ'mem hφ'refl
    let H : Subgroup G := H'.map L.subtype
    let d : G := (d' : G)
    let J : Subgroup G := J'.map L.subtype
    let eH : ↥H' ≃* ↥H := Subgroup.equivMapOfInjective H' L.subtype L.subtype_injective
    let φ : MulAut ↥H := MulAut.congr eH φ'
    have heH : ∀ b : ↥H', ((eH b : ↥H) : G) = (b : G) := fun b => rfl
    have hHL : H ≤ L := Subgroup.map_subtype_le H'
    have hdH : d ∈ H := Subgroup.mem_map_of_mem L.subtype hd'H'
    have hd1 : d ≠ 1 := by
      intro h
      exact hd'1 (Subtype.ext (show (d' : G) = 1 from h))
    have hHA : IsElemAbelian 3 H := hH'ea.map L.subtype
    have hHcard : Nat.card H = 3 ^ r := by
      rw [← hH'card]
      exact (Nat.card_congr eH.toEquiv).symm
    have hJ : CFSG.Assembly.IsComponentOf J
        (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
      have h1 := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (f := L.subtype) L.subtype_injective).2 hJ'
      rwa [map_subtype_centralizer_singleton_aux L d'] at h1
    have hφmem : φ ∈ ggAutomizer (L ⊓ Subgroup.centralizer ({d} : Set G)) H := by
      have h := mem_ggAutomizer_map_of_mem (f := L.subtype)
        (A := Subgroup.centralizer ({d'} : Set ↥L)) (B := H') (B' := H) rfl eH heH hφ'mem
      rw [map_subtype_centralizer_singleton_aux L d'] at h
      exact h
    have hφrefl : GGIsReflection 3 φ :=
      ggIsReflection_congr_of_mulEquiv eH hφ'refl.1 hφ'refl.2
    have hres := hIn H hHL hHA hHcard d hdH hd1 J hJ φ hφmem hφrefl
    rcases hres with hmem | hcomm
    · left
      obtain ⟨g, hgJ, hgN, hgind⟩ := mem_ggAutomizer_iff.mp hmem
      obtain ⟨g', hg'J', rfl⟩ := Subgroup.mem_map.mp hgJ
      refine mem_ggAutomizer_iff.mpr ⟨g', hg'J', ?_, ?_⟩
      · exact mem_normalizer_subgroupOf_of_map_subtype hgN
      · intro b'
        apply L.subtype_injective
        rw [map_mul, map_inv]
        have h2 : eH (φ' b') = φ (eH b') := by
          change eH (φ' b') = eH (φ' (eH.symm (eH b')))
          rw [MulEquiv.symm_apply_apply]
        calc L.subtype ((φ' b' : ↥H') : ↥L)
            = ((eH (φ' b') : ↥H) : G) := (heH (φ' b')).symm
          _ = ((φ (eH b') : ↥H) : G) := congrArg (fun y : ↥H => (y : G)) h2
          _ = L.subtype g' * L.subtype ((b' : ↥L)) * (L.subtype g')⁻¹ := by
                have h1 := hgind (eH b')
                rw [heH b'] at h1
                change ((φ (eH b') : ↥H) : G) =
                  L.subtype g' * L.subtype ((b' : ↥L)) * (L.subtype g')⁻¹ at h1
                exact h1
    · right
      intro ψ' hψ'mem
      have hψmem : MulAut.congr eH ψ' ∈ ggAutomizer J H :=
        mem_ggAutomizer_map_of_mem (f := L.subtype) (A := J') (B := H') (B' := H)
          rfl eH heH hψ'mem
      have hc := hcomm _ hψmem
      have hc' : MulAut.congr eH (φ' * ψ') = MulAut.congr eH (ψ' * φ') := by
        rw [map_mul, map_mul]
        exact hc
      exact (MulAut.congr eH).injective hc'
  · intro hCore H hHL hHA hHcard d hdH hd1 J hJ φ hφmem hφrefl
    let H' : Subgroup ↥L := H.subgroupOf L
    let d' : ↥L := ⟨d, hHL hdH⟩
    let J' : Subgroup ↥L := J.subgroupOf L
    let eH : ↥H' ≃* ↥H :=
      (Subgroup.equivMapOfInjective H' L.subtype L.subtype_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subgroupOf_eq_of_le hHL))
    let φ' : MulAut ↥H' := MulAut.congr eH.symm φ
    have heH : ∀ b' : ↥H', ((eH b' : ↥H) : G) = (b' : G) := fun b' => rfl
    have hd'H' : d' ∈ H' := by
      rw [Subgroup.mem_subgroupOf]
      exact hdH
    have hd'1 : d' ≠ 1 := by
      intro h
      exact hd1 (congrArg (fun x : ↥L => (x : G)) h)
    have hH'ea : IsElemAbelian 3 H' := hHA.subgroupOf L
    have hH'card : Nat.card H' = 3 ^ r := by
      rw [← hHcard]
      exact Nat.card_congr eH.toEquiv
    have hJleL : J ≤ L := hJ.1.trans inf_le_left
    have hJ' : CFSG.Assembly.IsComponentOf J'
        (Subgroup.centralizer ({d'} : Set ↥L)) := by
      refine (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (f := L.subtype) L.subtype_injective).mp ?_
      rw [map_subtype_centralizer_singleton_aux L d',
        Subgroup.map_subgroupOf_eq_of_le hJleL]
      exact hJ
    have hφeq : MulAut.congr eH φ' = φ := by
      ext b
      show ((eH ((MulAut.congr eH.symm φ) (eH.symm b)) : ↥H) : G) = ((φ b : ↥H) : G)
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
        MulEquiv.apply_symm_apply]
    have hφ'mem : φ' ∈ ggAutomizer (Subgroup.centralizer ({d'} : Set ↥L)) H' := by
      obtain ⟨g, hgC, hgN, hgind⟩ := mem_ggAutomizer_iff.mp hφmem
      have hgL : g ∈ L := hgC.1
      let g' : ↥L := ⟨g, hgL⟩
      have hg'C : g' ∈ Subgroup.centralizer ({d'} : Set ↥L) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        have hgd : g * d = d * g :=
          Subgroup.mem_centralizer_singleton_iff.mp
            (show g ∈ Subgroup.centralizer ({d} : Set G) from hgC.2)
        simpa only [Subgroup.coe_mul] using hgd
      have hg'N : g' ∈ Subgroup.normalizer (H' : Set ↥L) := by
        apply mem_normalizer_subgroupOf_of_map_subtype
        rw [Subgroup.map_subgroupOf_eq_of_le hHL]
        exact hgN
      refine mem_ggAutomizer_iff.mpr ⟨g', hg'C, hg'N, ?_⟩
      intro b'
      apply L.subtype_injective
      rw [map_mul, map_inv]
      have h2 : eH (φ' b') = φ (eH b') := by
        change eH ((MulAut.congr eH.symm φ) b') = φ (eH b')
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
          MulEquiv.apply_symm_apply]
      calc L.subtype ((φ' b' : ↥H') : ↥L)
          = ((eH (φ' b') : ↥H) : G) := (heH (φ' b')).symm
        _ = ((φ (eH b') : ↥H) : G) := congrArg (fun y : ↥H => (y : G)) h2
        _ = L.subtype g' * L.subtype ((b' : ↥L)) * (L.subtype g')⁻¹ := by
              have h1 := hgind (eH b')
              rw [heH b'] at h1
              change ((φ (eH b') : ↥H) : G) =
                L.subtype g' * L.subtype ((b' : ↥L)) * (L.subtype g')⁻¹ at h1
              exact h1
    have hφrefl' : GGIsReflection 3 φ' :=
      ggIsReflection_congr_of_mulEquiv (G := ↥L) (A := H') eH.symm hφrefl.1 hφrefl.2
    have hres := hCore H' hH'ea hH'card d' hd'H' hd'1 J' hJ' φ' hφ'mem hφrefl'
    rcases hres with hmem | hcomm
    · left
      have h := mem_ggAutomizer_map_of_mem (f := L.subtype) (A := J') (B := H') (B' := H)
        (Subgroup.map_subgroupOf_eq_of_le hHL) eH heH hmem
      rw [Subgroup.map_subgroupOf_eq_of_le hJleL, hφeq] at h
      exact h
    · right
      intro ψ hψmem
      obtain ⟨j, hjJ, hjN, hjind⟩ := mem_ggAutomizer_iff.mp hψmem
      have hjJ' : j ∈ J'.map L.subtype := by
        rw [Subgroup.map_subgroupOf_eq_of_le hJleL]
        exact hjJ
      obtain ⟨g', hg'J', rfl⟩ := Subgroup.mem_map.mp hjJ'
      have hψeq : MulAut.congr eH (MulAut.congr eH.symm ψ) = ψ := by
        ext b
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
          MulEquiv.apply_symm_apply]
      have hψ'mem : MulAut.congr eH.symm ψ ∈ ggAutomizer J' H' := by
        refine mem_ggAutomizer_iff.mpr ⟨g', hg'J', ?_, ?_⟩
        · apply mem_normalizer_subgroupOf_of_map_subtype
          rw [Subgroup.map_subgroupOf_eq_of_le hHL]
          exact hjN
        · intro b'
          apply L.subtype_injective
          rw [map_mul, map_inv]
          have h2 : eH (MulAut.congr eH.symm ψ b') = ψ (eH b') := by
            simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
              MulEquiv.apply_symm_apply]
          calc L.subtype (((MulAut.congr eH.symm ψ) b' : ↥H') : ↥L)
              = ((eH ((MulAut.congr eH.symm ψ) b') : ↥H) : G) :=
                (heH ((MulAut.congr eH.symm ψ) b')).symm
            _ = ((ψ (eH b') : ↥H) : G) := congrArg (fun y : ↥H => (y : G)) h2
            _ = L.subtype g' * L.subtype ((b' : ↥L)) * (L.subtype g')⁻¹ := by
                  have h1 := hjind (eH b')
                  rw [heH b'] at h1
                  change ((ψ (eH b') : ↥H) : G) =
                    L.subtype g' * L.subtype ((b' : ↥L)) * (L.subtype g')⁻¹ at h1
                  exact h1
      have hc := hcomm _ hψ'mem
      have hc' : MulAut.congr eH φ' * ψ = ψ * MulAut.congr eH φ' := by
        have h := congrArg (MulAut.congr eH) hc
        rwa [map_mul, map_mul, hψeq] at h
      rwa [hφeq] at hc'

end CFSG.StandardType

end
