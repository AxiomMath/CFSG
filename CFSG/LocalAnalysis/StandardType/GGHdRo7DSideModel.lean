module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideDirs
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelH
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelI

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

private noncomputable def hdRo7DDSdMAux_zmodZpowersEquiv {G : Type} [Group G] [Finite G] {z : G}
    (p : ℕ) (hzp : z ^ p = 1) (hz : z ≠ 1) (hp : Nat.Prime p) :
    Multiplicative (ZMod p) ≃* Subgroup.zpowers z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let φ : Multiplicative (ZMod p) →* Subgroup.zpowers z :=
    { toFun := fun m => ⟨z ^ (Multiplicative.toAdd m).val,
        Subgroup.pow_mem _ (Subgroup.mem_zpowers z) (Multiplicative.toAdd m).val⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        show z ^ (Multiplicative.toAdd (a * b)).val =
          z ^ (Multiplicative.toAdd a).val * z ^ (Multiplicative.toAdd b).val
        rw [show Multiplicative.toAdd (a * b) =
            Multiplicative.toAdd a + Multiplicative.toAdd b from rfl,
          ZMod.val_add, ← pow_eq_pow_mod _ hzp, pow_add] }
  have hdom : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]
  have hcod : Nat.card ↥(Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzp hz]
  have hne : φ.ker ≠ ⊤ := by
    intro h
    have h1 : φ (Multiplicative.ofAdd (1 : ZMod p)) = 1 := by
      have : Multiplicative.ofAdd (1 : ZMod p) ∈ φ.ker := by
        rw [h]; exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mp this
    have h2 : φ (Multiplicative.ofAdd (1 : ZMod p)) = ⟨z, Subgroup.mem_zpowers z⟩ := by
      apply Subtype.ext
      show z ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = z
      rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p)) = (1 : ZMod p) from rfl,
        ZMod.val_one, pow_one]
    rw [h2] at h1
    exact hz (congrArg Subtype.val h1)
  have hcardker : Nat.card φ.ker = 1 := by
    have hdvd : Nat.card φ.ker ∣ p := by
      have := Subgroup.card_subgroup_dvd_card φ.ker
      rwa [hdom] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact h1
    · exfalso
      apply hne
      exact Subgroup.eq_top_of_card_eq _ (by rw [h1, hdom])
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hcardker
  have hrange : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h := CFSG.StandardType.TableB.card_range_mul_card_ker φ
    rw [hcardker, mul_one, hdom] at h
    rw [h, hcod]
  exact MulEquiv.ofBijective φ ⟨hinj, MonoidHom.range_eq_top.mp hrange⟩

private noncomputable def hdRo7DDSdMAux_tauC {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {z : G}
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z)
    (hzp : z ^ p = 1) (hz1 : z ≠ 1) (hp : Nat.Prime p) :
    Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
  (hdRo7DDSdMAux_zmodZpowersEquiv p hzp hz1 hp).trans (MulEquiv.subgroupCongr hC).symm

private theorem hdRo7DDSdMAux_tauC_apply {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {z : G}
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z)
    (hzp : z ^ p = 1) (hz1 : z ≠ 1) (hp : Nat.Prime p) :
    ∀ m : Multiplicative (ZMod p),
      (hdRo7DDSdMAux_tauC hC hzp hz1 hp m : G) =
        z ^ (Multiplicative.toAdd m).val :=
  fun _ => rfl

private def hdRo7DDSdMAux_prodHom {G : Type} [Group G] (Bs X : Subgroup G) :
    ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) →* ↥Bs where
  toFun q := ⟨(q.1 : G) * (q.2 : G), Bs.mul_mem q.1.2.1 q.2.2.1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' q r := by
    apply Subtype.ext
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    have h : (r.1 : G) * (q.2 : G) = (q.2 : G) * (r.1 : G) :=
      Subgroup.mem_centralizer_iff.mp q.2.2.2 (r.1 : G) r.1.2.2
    calc ((q.1 : G) * (r.1 : G)) * ((q.2 : G) * (r.2 : G))
        = (q.1 : G) * ((r.1 : G) * (q.2 : G)) * (r.2 : G) := by group
      _ = (q.1 : G) * ((q.2 : G) * (r.1 : G)) * (r.2 : G) := by rw [h]
      _ = ((q.1 : G) * (q.2 : G)) * ((r.1 : G) * (r.2 : G)) := by group

private theorem hdRo7DDSdMAux_eq_one_of_mem_inf_centralizer {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hcop : ¬ p ∣ Nat.card (Subgroup.center ↥X)) {u : G} (huBs : u ∈ Bs) (huX : u ∈ X)
    (huC : u ∈ Subgroup.centralizer (X : Set G)) : u = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hup : u ^ p = 1 := hBs.2.1.2 u huBs
  have hupX : (⟨u, huX⟩ : ↥X) ^ p = 1 := by
    apply Subtype.ext
    simpa using hup
  have hcenter : (⟨u, huX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp huC (w : G) w.2
  have hdvd : orderOf (⟨u, huX⟩ : ↥X) ∣ Nat.card ↥(Subgroup.center ↥X) :=
    Subgroup.orderOf_dvd_natCard _ hcenter
  have hdvdp : orderOf (⟨u, huX⟩ : ↥X) ∣ p := orderOf_dvd_of_pow_eq_one hupX
  have h1 : orderOf (⟨u, huX⟩ : ↥X) = 1 := by
    rcases (Nat.dvd_prime hp).mp hdvdp with h | h
    · exact h
    · exfalso
      rw [h] at hdvd
      exact hcop hdvd
  have hone : (⟨u, huX⟩ : ↥X) = 1 := orderOf_eq_one_iff.mp h1
  simpa using congrArg Subtype.val hone

private theorem hdRo7DDSdMAux_prodHom_bijective {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hsplit : ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ X, ∃ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), b = t * c)
    (hcop : ¬ p ∣ Nat.card (Subgroup.center ↥X)) :
    Function.Bijective (hdRo7DDSdMAux_prodHom Bs X) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨t, ht⟩, ⟨c, hc⟩⟩ ⟨⟨t', ht'⟩, ⟨c', hc'⟩⟩ heq
    have h' : (t : G) * (c : G) = (t' : G) * (c' : G) := congrArg Subtype.val heq
    have hu : t'⁻¹ * t = c' * c⁻¹ := by
      calc t'⁻¹ * t = t'⁻¹ * (t * c) * c⁻¹ := by group
        _ = t'⁻¹ * (t' * c') * c⁻¹ := by rw [h']
        _ = c' * c⁻¹ := by group
    have huBs : t'⁻¹ * t ∈ Bs := Bs.mul_mem (Bs.inv_mem ht'.1) ht.1
    have huX : t'⁻¹ * t ∈ X := X.mul_mem (X.inv_mem ht'.2) ht.2
    have huC : t'⁻¹ * t ∈ Subgroup.centralizer (X : Set G) := by
      rw [hu]
      exact (Subgroup.centralizer (X : Set G)).mul_mem hc'.2
        ((Subgroup.centralizer (X : Set G)).inv_mem hc.2)
    have hu1 : t'⁻¹ * t = 1 :=
      hdRo7DDSdMAux_eq_one_of_mem_inf_centralizer hp hBs hcop huBs huX huC
    have htt : t = t' := by
      calc t = t' * (t'⁻¹ * t) := by group
        _ = t' * 1 := by rw [hu1]
        _ = t' := by group
    have hcc : c = c' := by
      apply mul_left_cancel (a := t')
      rw [htt] at h'
      exact h'
    exact Prod.ext (Subtype.ext htt) (Subtype.ext hcc)
  · intro b
    obtain ⟨t, htT, c, hcC, hbc⟩ := hsplit (b : G) b.2
    refine ⟨(⟨t, htT⟩, ⟨c, hcC⟩), Subtype.ext ?_⟩
    show (t : G) * (c : G) = (b : G)
    simpa using hbc.symm

private noncomputable def hdRo7DDSdMAux_prodEquiv {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hsplit : ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ X, ∃ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), b = t * c)
    (hcop : ¬ p ∣ Nat.card (Subgroup.center ↥X)) :
    ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≃* ↥Bs :=
  MulEquiv.ofBijective (hdRo7DDSdMAux_prodHom Bs X)
    (hdRo7DDSdMAux_prodHom_bijective hp hBs hsplit hcop)

private noncomputable def hdRo7DDSdMAux_subgroupOfEquiv {G : Type} [Group G] (Bs X : Subgroup G) :
    ↥(Bs.subgroupOf X) ≃* ↥(Bs ⊓ X) where
  toFun y := ⟨((y : ↥X) : G), ⟨y.2, (y : ↥X).2⟩⟩
  invFun t := ⟨⟨(t : G), t.2.2⟩, t.2.1⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem hdRo7DDSdMAux_selfCentralizing {G : Type} [Group G] {p : ℕ} {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs)
    (hsplit : ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ X, ∃ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), b = t * c) :
    ∀ g : ↥X, (∀ e ∈ Bs.subgroupOf X, g * e = e * g) → g ^ p = 1 → g ∈ Bs.subgroupOf X := by
  intro g hcen hgp
  have hgp' : (g : G) ^ p = 1 := by
    simpa using congrArg (fun y : ↥X => (y : G)) hgp
  have hmemT : ∀ t : ↥(Bs ⊓ X), (t : G) * (g : G) = (g : G) * (t : G) := by
    intro t
    have hmemE : (⟨(t : G), t.2.2⟩ : ↥X) ∈ Bs.subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr t.2.1
    exact (congrArg (fun y : ↥X => (y : G)) (hcen ⟨(t : G), t.2.2⟩ hmemE)).symm
  have hmemC : ∀ c : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)),
      (c : G) * (g : G) = (g : G) * (c : G) := by
    intro c
    exact (Subgroup.mem_centralizer_iff.mp c.2.2 (g : G) g.2).symm
  refine Subgroup.mem_subgroupOf.mpr (hBs.2.2.2 (g : G) ?_ hgp')
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨t, ht, c, hc, rfl⟩ := hsplit b hb
  calc (t : G) * (c : G) * (g : G) = (t : G) * ((c : G) * (g : G)) := by group
    _ = (t : G) * ((g : G) * (c : G)) := by rw [hmemC ⟨c, hc⟩]
    _ = ((t : G) * (g : G)) * (c : G) := by group
    _ = ((g : G) * (t : G)) * (c : G) := by rw [hmemT ⟨t, ht⟩]
    _ = (g : G) * ((t : G) * (c : G)) := by group

private theorem hdRo7DDSdMAux_conj_eq {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} {k : ℕ}
    {τE : (Fin k → Multiplicative (ZMod p)) →* ↥X}
    {τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ X)}
    (hτTcoe : ∀ f, ((τT f : ↥(Bs ⊓ X)) : G) = ((τE f : ↥X) : G))
    {g : ↥X} {f f' : Fin k → Multiplicative (ZMod p)}
    (h : (g : G) * (τT f : G) * (g : G)⁻¹ = (τT f' : G)) :
    g * τE f * g⁻¹ = τE f' := by
  apply Subtype.ext
  simpa [hτTcoe] using h

private theorem hdRo7DDSdMAux_transfer {G : Type} [Group G] {p : ℕ} (Bs X : Subgroup G) (k : ℕ)
    (τE : (Fin k → Multiplicative (ZMod p)) →* ↥X)
    (hτEinj : Function.Injective τE) (hτErange : τE.range = Bs.subgroupOf X) :
    ∃ τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ X),
      Function.Bijective τT ∧
      (∀ f, ((τT f : ↥(Bs ⊓ X)) : G) = ((τE f : ↥X) : G)) ∧
      (∀ (φ : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p)))
        (w : ↥X), (∀ f, w * τE f * w⁻¹ = τE (φ f)) →
        ∀ f, (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (φ f) : G)) ∧
      (∀ g : ↥X, (∀ e : ↥(Bs ⊓ X), ∃ e' : ↥(Bs ⊓ X),
          (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
        ∀ e ∈ Bs.subgroupOf X, g * e * g⁻¹ ∈ Bs.subgroupOf X) := by
  have hmemBs : ∀ f, ((τE f : ↥X) : G) ∈ Bs := by
    intro f
    have h : τE f ∈ τE.range := MonoidHom.mem_range.mpr ⟨f, rfl⟩
    rw [hτErange] at h
    exact Subgroup.mem_subgroupOf.mp h
  let τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ X) :=
    { toFun := fun f => ⟨((τE f : ↥X) : G), ⟨hmemBs f, (τE f).2⟩⟩
      map_one' := by
        apply Subtype.ext
        change ((τE 1 : ↥X) : G) = ((1 : ↥(Bs ⊓ X)) : G)
        rw [map_one]
        rfl
      map_mul' := fun f f' => by
        apply Subtype.ext
        change ((τE (f * f') : ↥X) : G) = ((τE f : ↥X) : G) * ((τE f' : ↥X) : G)
        rw [map_mul]
        rfl }
  have hτTcoe : ∀ f, ((τT f : ↥(Bs ⊓ X)) : G) = ((τE f : ↥X) : G) := fun _ => rfl
  have hbij : Function.Bijective τT := by
    refine ⟨?_, ?_⟩
    · intro f f' hff
      apply hτEinj
      apply Subtype.ext
      have h : ((τT f : ↥(Bs ⊓ X)) : G) = ((τT f' : ↥(Bs ⊓ X)) : G) :=
        congrArg Subtype.val hff
      rwa [hτTcoe f, hτTcoe f'] at h
    · intro t
      have hmemE : (⟨(t : G), t.2.2⟩ : ↥X) ∈ Bs.subgroupOf X :=
        Subgroup.mem_subgroupOf.mpr t.2.1
      have h : (⟨(t : G), t.2.2⟩ : ↥X) ∈ τE.range := by
        rw [hτErange]
        exact hmemE
      obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp h
      refine ⟨f, Subtype.ext ?_⟩
      change ((τE f : ↥X) : G) = (t : G)
      exact congrArg Subtype.val hf
  refine ⟨τT, hbij, hτTcoe, ?_, ?_⟩
  · intro φ w hw f
    have h := congrArg (fun y : ↥X => (y : G)) (hw f)
    simpa [hτTcoe] using h
  · intro g hg e he
    obtain ⟨e', he'⟩ := hg ⟨(e : G), ⟨Subgroup.mem_subgroupOf.mp he, e.2⟩⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    have h1 : ((g * e * g⁻¹ : ↥X) : G) = (e' : G) := by
      calc ((g * e * g⁻¹ : ↥X) : G) = (g : G) * (e : G) * (g : G)⁻¹ := by simp
        _ = (e' : G) := he'
    rw [h1]
    exact e'.2.1

theorem d_coordModel_of_frame {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hsplit : ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ X, ∃ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), b = t * c)
    (hcop : ¬ p ∣ Nat.card (Subgroup.center ↥X)) {z : G} (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z)
    (h4 : p ^ 4 ≤ Nat.card Bs) {ℓ : ℕ} (hfr : GGTorusOrthFrameSC p ↥X ℓ) :
    ∃ (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨z, hz⟩ ∧
      ((n = ℓ ∧ DCoordModel p Bs X n τ) ∨ (n + 1 = ℓ ∧ C2CoordModel p Bs X n τ)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hzp : z ^ p = 1 := hBs.2.1.2 z hz
  let Φ := hdRo7DDSdMAux_prodEquiv hp hBs hsplit hcop
  have hΦ : ∀ (t : ↥(Bs ⊓ X)) (c : ↥(Bs ⊓ Subgroup.centralizer (X : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G) := fun _ _ => rfl
  have hCcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = p := by
    rw [hC, Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  have hBscard : Nat.card ↥Bs = Nat.card ↥(Bs ⊓ X) * p := by
    have h1 : Nat.card ↥Bs =
        Nat.card (↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) :=
      (Nat.card_congr Φ.toEquiv).symm
    rw [h1, Nat.card_prod, hCcard]
  have hTcard : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X) := by
    have hmul : p ^ 3 * p ≤ Nat.card ↥(Bs ⊓ X) * p := by
      have hp4 : p ^ 3 * p = p ^ 4 := by rw [← pow_succ]
      rw [hp4]
      exact le_trans h4 (le_of_eq hBscard)
    exact Nat.le_of_mul_le_mul_right hmul hp.pos
  have hEea : IsElemAbelian p (Bs.subgroupOf X) :=
    CFSG.Open.IsElemAbelian.subgroupOf (K := X) hBs.2.1
  have hEcard : Nat.card ↥(Bs.subgroupOf X) = Nat.card ↥(Bs ⊓ X) :=
    Nat.card_congr (hdRo7DDSdMAux_subgroupOfEquiv Bs X).toEquiv
  have hcardE : p ^ 3 ≤ Nat.card ↥(Bs.subgroupOf X) := by
    rw [hEcard]
    exact hTcard
  obtain ⟨k, τE, hτEinj, hτErange, hpermF, hcases⟩ :=
    hfr (Bs.subgroupOf X) hEea hcardE (hdRo7DDSdMAux_selfCentralizing hBs hsplit)
  obtain ⟨τT, hτTbij, hτTcoe, hconj, hnormE⟩ :=
    hdRo7DDSdMAux_transfer Bs X k τE hτEinj hτErange
  let τC := hdRo7DDSdMAux_tauC hC hzp hz1 hp
  have hτCapply : ∀ m : Multiplicative (ZMod p),
      (τC m : G) = z ^ (Multiplicative.toAdd m).val :=
    fun m => hdRo7DDSdMAux_tauC_apply hC hzp hz1 hp m
  let τ := hdRo7CLCoordAux_tau p B Bs z X k τT hτTbij τC Φ
  have hτz : τ (Pi.mulSingle (0 : Fin (k + 1)) (Multiplicative.ofAdd (1 : ZMod p))) =
      ⟨z, hz⟩ := by
    obtain ⟨hz', hz'eq⟩ :=
      hdRo7CLCoordAux_tau_mulSingle p B Bs z X k τT hτTbij τC Φ hΦ hτCapply hp hzp hz
    exact hz'eq.trans (Subtype.ext rfl)
  have hLx : ∀ g : ↥X, (g : G) * z * (g : G)⁻¹ = z := by
    intro g
    have hzC : z ∈ Subgroup.centralizer (X : Set G) := by
      have h : z ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
        rw [hC]
        exact Subgroup.mem_zpowers z
      exact h.2
    have hcomm : (g : G) * z = z * (g : G) :=
      Subgroup.mem_centralizer_iff.mp hzC (g : G) g.2
    rw [hcomm]
    group
  have hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥X, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.permAut σ f) : G) := by
    intro σ
    obtain ⟨w, hw⟩ := hpermF σ
    exact ⟨w, hconj (SpCoord.permAut σ) w hw⟩
  refine ⟨k, τ, hτz, ?_⟩
  rcases hcases with ⟨hk, hdinvF, hnormF⟩ | ⟨hk, hsgnF, hnormF⟩
  · left
    have hdinv : ∀ i j : Fin k, i ≠ j → ∃ w : ↥X, ∀ f,
        (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (NbrOrth.dinv i j f) : G) := by
      intro i j hij
      obtain ⟨w, hw⟩ := hdinvF i j hij
      exact ⟨w, hconj (NbrOrth.dinv i j) w hw⟩
    have hnorm : ∀ g : ↥X, (∀ e : ↥(Bs ⊓ X), ∃ e' : ↥(Bs ⊓ X),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
          (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∏ i, ε i = 1 ∧
          ∀ f f', (g : G) * (τT f : G) * (g : G)⁻¹ = (τT f' : G) →
            ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i) := by
      intro g hgN
      obtain ⟨π, ε, hε, hprod, hrel⟩ := hnormF g (hnormE g hgN)
      exact ⟨π, ε, hε, hprod, fun f f' hff => hrel f f' (hdRo7DDSdMAux_conj_eq hτTcoe hff)⟩
    refine ⟨hk, ?_⟩
    exact d_dcoordModel_tau_of_dirs p B Bs z X k τT hτTbij τC Φ hΦ hτCapply hdinv hperm
      hnorm hLx hzp hz1 hp hz
  · right
    have hsgn : ∀ i : Fin k, ∃ w : ↥X, ∀ f,
        (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.sgnAut i f) : G) := by
      intro i
      obtain ⟨w, hw⟩ := hsgnF i
      exact ⟨w, hconj (SpCoord.sgnAut i) w hw⟩
    have hnorm : ∀ g : ↥X, (∀ e : ↥(Bs ⊓ X), ∃ e' : ↥(Bs ⊓ X),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', (g : G) * (τT f : G) * (g : G)⁻¹ = (τT f' : G) →
            ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i) := by
      intro g hgN
      obtain ⟨π, ε, hε, hrel⟩ := hnormF g (hnormE g hgN)
      exact ⟨π, ε, hε, fun f f' hff => hrel f f' (hdRo7DDSdMAux_conj_eq hτTcoe hff)⟩
    refine ⟨hk, ?_⟩
    exact hdRo7CLCoordAux_coordModel_tau_of_dirs p B Bs z X k τT hτTbij τC Φ hΦ
      hτCapply hsgn hperm hnorm hLx hzp hz1 hp hz

end CFSG.StandardType.HdRo7D
