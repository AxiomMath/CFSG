module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Core
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Sec
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

private structure L2Setup {Q : Type} [Group Q] {V : Type} [CommGroup V]
    (ρ : Q →* MulAut V) (L A : Subgroup Q) where
  W : Subgroup V
  Lbar : Subgroup (MulAut (V ⧸ W))
  Abar : Subgroup (MulAut (V ⧸ W))
  hstabA : ∀ a ∈ A, ρ a ∈ stabSub W
  hstabL : ∀ l ∈ L, ρ l ∈ stabSub W
  e : ↥L ≃* ↥Lbar
  eA : ↥A ≃* ↥Abar
  he : ∀ l : ↥L, (e l : MulAut (V ⧸ W)) =
    quotHom W ⟨ρ (l : Q), hstabL l.1 l.2⟩
  heA : ∀ a : ↥A, (eA a : MulAut (V ⧸ W)) =
    quotHom W ⟨ρ (a : Q), hstabA a.1 a.2⟩
  hLbar : IsSimpleGroup ↥Lbar
  hZbar : Subgroup.center ↥Lbar = ⊥
  hXbar : L2AutFacts ↥Lbar
  hALbar : Abar ≤ Subgroup.normalizer (Lbar : Set (MulAut (V ⧸ W)))
  hA4bar : Nat.card Abar = 4
  hA2bar : ∀ a ∈ Abar, a * a = 1
  hquadAbar : IsQuadratic Abar
  hACbar : Abar ⊓ Subgroup.centralizer (Lbar : Set (MulAut (V ⧸ W))) = ⊥
  hfixLbar : fixV Lbar = ⊥
  hVquot : ∀ v : V ⧸ W, v ^ 2 = 1
  key : ∀ (x : Q), x ∈ Subgroup.normalizer (L : Set Q) → (g : stabSub W) →
    ρ x = (g : MulAut V) →
    (∀ l : ↥L, (quotHom W g : MulAut (V ⧸ W)) * (e l : MulAut (V ⧸ W)) =
      (e l : MulAut (V ⧸ W)) * (quotHom W g : MulAut (V ⧸ W))) →
    x ∈ Subgroup.centralizer (L : Set Q)

private noncomputable def L2Setup.ofRep {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ρ : Q →* MulAut V) (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hL : IsSimpleGroup ↥L) (hZ : Subgroup.center ↥L = ⊥)
    (hX : L2AutFacts ↥L) (hAL : A ≤ Subgroup.normalizer (L : Set Q))
    (hA4 : Nat.card A = 4) (hA2 : ∀ a ∈ A, a * a = 1)
    (hq : CFSG.LocalAnalysis.WeakClosure81.IsQuadraticOn ρ A)
    (hAC : A ⊓ Subgroup.centralizer (L : Set Q) = ⊥) : L2Setup ρ L A := by
  classical
  let L₁ : Subgroup (MulAut V) := L.map ρ
  let A₁ : Subgroup (MulAut V) := A.map ρ
  let G : Subgroup (MulAut V) := A₁ ⊔ L₁
  have hrange : (ρ.comp L.subtype).range = L₁ := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, l.2, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  have hperfect : Group.IsPerfect ↥L := by
    have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
      by_contra h
      have hcomm : ∀ a b : ↥L, a * b = b * a := by
        intro a b
        by_contra hab
        exact h ⟨a, b, hab⟩
      haveI : IsMulCommutative ↥L := isMulCommutative_iff.mpr hcomm
      have htop : Subgroup.center ↥L = ⊤ := Subgroup.center_eq_top_iff.mpr inferInstance
      rw [hZ] at htop
      exact bot_ne_top htop
    exact TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative
      (fun hc => let ⟨a, b, hab⟩ := hnab; hab (hc.is_comm.comm a b))
  have hperfMap : (commutator ↥L).map (ρ.comp L.subtype) = ⁅L₁, L₁⁆ := by
    rw [map_commutator_eq, hrange]
  have hperfL₁ : ⁅L₁, L₁⁆ = L₁ := by
    rw [← hperfMap, Group.isPerfect_def.mp hperfect, ← MonoidHom.range_eq_map, hrange]
  haveI : IsSimpleGroup ↥L := hL
  have hLne : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
  have hL₁ne : L₁ ≠ ⊥ := by
    intro hbot
    apply hLne
    exact (Subgroup.map_eq_bot_iff_of_injective L hρ).mp hbot
  have hA₁leG : A₁ ≤ G := le_sup_left
  have hL₁leG : L₁ ≤ G := le_sup_right
  have hA₁norm : A₁ ≤ Subgroup.normalizer (L₁ : Set (MulAut V)) :=
    (Subgroup.map_mono hAL).trans (Subgroup.le_normalizer_map ρ)
  have hL₁norm : L₁ ≤ Subgroup.normalizer (L₁ : Set (MulAut V)) := Subgroup.le_normalizer
  have hGnorm : G ≤ Subgroup.normalizer (L₁ : Set (MulAut V)) :=
    sup_le hA₁norm hL₁norm
  have hnorm : ∀ g ∈ G, ∀ l ∈ L₁, g * l * g⁻¹ ∈ L₁ := by
    intro g hg l hl
    exact (Subgroup.mem_normalizer_iff.mp (hGnorm hg) l).mp hl
  let W : Subgroup V :=
    Classical.choose (exists_quot_fixV_eq_bot hL₁leG hnorm hperfL₁ hL₁ne)
  have hWspec :=
    Classical.choose_spec (exists_quot_fixV_eq_bot hL₁leG hnorm hperfL₁ hL₁ne)
  obtain ⟨hGW, hWnon, hfixW⟩ := hWspec
  have hstabA₁ : A₁ ≤ stabSub W := hA₁leG.trans hGW
  have hstabL₁ : L₁ ≤ stabSub W := hL₁leG.trans hGW
  have hstabA : ∀ a ∈ A, ρ a ∈ stabSub W := fun a ha =>
    hstabA₁ (Subgroup.mem_map_of_mem ρ ha)
  have hstabL : ∀ l ∈ L, ρ l ∈ stabSub W := fun l hl =>
    hstabL₁ (Subgroup.mem_map_of_mem ρ hl)
  let ι : ↥L →* stabSub W :=
    { toFun := fun l => ⟨ρ (l : Q), hstabL l.1 l.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  let f : ↥L →* MulAut (V ⧸ W) := (quotHom W).comp ι
  let Lbar : Subgroup (MulAut (V ⧸ W)) := autQuot L₁ W
  let Abar : Subgroup (MulAut (V ⧸ W)) := autQuot A₁ W
  let θ : ↥L →* ↥Lbar :=
    f.codRestrict Lbar fun l =>
      mem_autQuot.mpr ⟨ι l, ⟨l, l.2, rfl⟩, rfl⟩
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨g, hgA, hgx⟩ := mem_autQuot.mp x.2
    obtain ⟨l, hl, hgl⟩ := Subgroup.mem_map.mp hgA
    refine ⟨⟨l, hl⟩, ?_⟩
    apply Subtype.ext
    change quotHom W (ι ⟨l, hl⟩) = (x : MulAut (V ⧸ W))
    rw [show ι ⟨l, hl⟩ = g from Subtype.ext hgl]
    exact hgx
  have hθker : θ.ker = ⊥ := by
    rcases hL.eq_bot_or_eq_top_of_normal θ.ker with h | h
    · exact h
    · exfalso
      apply hWnon
      intro x hx
      obtain ⟨l, hl, hxl⟩ := Subgroup.mem_map.mp hx
      have h1 : (⟨l, hl⟩ : ↥L) ∈ θ.ker := by rw [h]; trivial
      have h2 : (θ ⟨l, hl⟩ : ↥Lbar) = 1 := MonoidHom.mem_ker.mp h1
      have h3 : quotHom W (ι ⟨l, hl⟩) = 1 := congrArg Subtype.val h2
      have h4 : ι ⟨l, hl⟩ ∈ (quotHom W).ker := MonoidHom.mem_ker.mpr h3
      rw [ker_quotHom] at h4
      have h5 : (ι ⟨l, hl⟩ : MulAut V) ∈ centQuot W := Subgroup.mem_subgroupOf.mp h4
      exact hxl ▸ h5
  have hθinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).mp hθker
  let e : ↥L ≃* ↥Lbar := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  have hLbar : IsSimpleGroup ↥Lbar := e.symm.isSimpleGroup
  have hZbar : Subgroup.center ↥Lbar = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [hZ, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hXbar : L2AutFacts ↥Lbar := hX.of_mulEquiv e
  have key : ∀ (x : Q), x ∈ Subgroup.normalizer (L : Set Q) → (g : stabSub W) →
      ρ x = (g : MulAut V) →
      (∀ l : ↥L, (quotHom W g : MulAut (V ⧸ W)) * (e l : MulAut (V ⧸ W)) =
        (e l : MulAut (V ⧸ W)) * (quotHom W g : MulAut (V ⧸ W))) →
      x ∈ Subgroup.centralizer (L : Set Q) := by
    intro x hx g hgx hcomm l hl
    let ψ : MulAut ↥L := conjAct L ⟨x, hx⟩
    have hψcoe : ∀ l : ↥L, ((ψ l : ↥L) : Q) = x * (l : Q) * x⁻¹ := fun l =>
      CFSG.Quasithin.AutOn.coe_conjAct_apply L ⟨x, hx⟩ l
    have hθconj : ∀ l : ↥L,
        (e (ψ l) : MulAut (V ⧸ W)) = (quotHom W g : MulAut (V ⧸ W)) *
          (e l : MulAut (V ⧸ W)) * (quotHom W g : MulAut (V ⧸ W))⁻¹ := by
      intro l
      have hsub : ι (ψ l) = g * ι l * g⁻¹ := by
        apply Subtype.ext
        change ρ ((ψ l : ↥L) : Q) = (g : MulAut V) * ρ (l : Q) * (g : MulAut V)⁻¹
        have h := congrArg (fun z : Q => ρ z) (hψcoe l)
        simpa [map_mul, hgx] using h
      calc (e (ψ l) : MulAut (V ⧸ W)) = quotHom W (ι (ψ l)) := rfl
        _ = quotHom W (g * ι l * g⁻¹) := by rw [hsub]
        _ = (quotHom W g : MulAut (V ⧸ W)) * (quotHom W (ι l) : MulAut (V ⧸ W)) *
              (quotHom W g : MulAut (V ⧸ W))⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = (quotHom W g : MulAut (V ⧸ W)) * (e l : MulAut (V ⧸ W)) *
              (quotHom W g : MulAut (V ⧸ W))⁻¹ := rfl
    have hψl : ∀ l : ↥L, ψ l = l := by
      intro l
      apply e.injective
      apply Subtype.ext
      change (e (ψ l) : MulAut (V ⧸ W)) = (e l : MulAut (V ⧸ W))
      rw [hθconj l, hcomm l]
      group
    have h2 : x * l * x⁻¹ = l := by
      have h := congrArg (fun z : ↥L => (z : Q)) (hψl ⟨l, hl⟩)
      rw [hψcoe] at h
      simpa using h
    calc l * x = (x * l * x⁻¹) * x := by rw [h2]
      _ = x * l := by group
  have he : ∀ l : ↥L, (e l : MulAut (V ⧸ W)) =
      quotHom W ⟨ρ (l : Q), hstabL l.1 l.2⟩ := fun l => rfl
  let ιA : ↥A →* stabSub W :=
    { toFun := fun a => ⟨ρ (a : Q), hstabA a.1 a.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  let fA : ↥A →* MulAut (V ⧸ W) := (quotHom W).comp ιA
  let θA : ↥A →* ↥Abar :=
    fA.codRestrict Abar fun a =>
      mem_autQuot.mpr ⟨ιA a, ⟨a, a.2, rfl⟩, rfl⟩
  have hA_surj : Function.Surjective θA := by
    intro x
    obtain ⟨g, hgA, hgx⟩ := mem_autQuot.mp x.2
    obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hgA
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    change quotHom W (ιA ⟨a, ha⟩) = (x : MulAut (V ⧸ W))
    rw [show ιA ⟨a, ha⟩ = g from Subtype.ext hga]
    exact hgx
  have hA_inj : Function.Injective θA := by
    intro a b hab
    have h1 : θA (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : quotHom W (ιA (a * b⁻¹)) = 1 := congrArg Subtype.val h1
    have hkey := key ((a * b⁻¹ : ↥A) : Q) ?_ (ιA (a * b⁻¹)) rfl ?_
    · have hu : ((a * b⁻¹ : ↥A) : Q) ∈ A ⊓ Subgroup.centralizer (L : Set Q) :=
        ⟨(a * b⁻¹).2, hkey⟩
      rw [hAC, Subgroup.mem_bot] at hu
      exact mul_inv_eq_one.mp (Subtype.ext hu)
    · exact (Subgroup.normalizer (L : Set Q)).mul_mem (hAL a.2)
        ((Subgroup.normalizer (L : Set Q)).inv_mem (hAL b.2))
    · intro l
      rw [h2]
      simp
  let eA : ↥A ≃* ↥Abar := MulEquiv.ofBijective θA ⟨hA_inj, hA_surj⟩
  have hA4bar : Nat.card Abar = 4 := by
    have hcard := Nat.card_congr eA.toEquiv
    rw [hA4] at hcard
    exact hcard.symm
  have hA2bar : ∀ u ∈ Abar, u * u = 1 := by
    intro u hu
    obtain ⟨a, ha⟩ := hA_surj ⟨u, hu⟩
    have hcoe : (θA a : MulAut (V ⧸ W)) = u := congrArg Subtype.val ha
    rw [← hcoe, ← Subgroup.coe_mul, ← map_mul]
    have h2 : a * a = 1 := by
      apply Subtype.ext
      exact hA2 (a : Q) a.2
    rw [h2, map_one]
    simp
  have hALbar_one : ∀ u ∈ Abar, ∀ l ∈ Lbar, u * l * u⁻¹ ∈ Lbar := by
    intro u hu l hl
    obtain ⟨g, hgA, hgu⟩ := mem_autQuot.mp hu
    obtain ⟨l₀, hl₀, hgl⟩ := mem_autQuot.mp hl
    rw [← hgu, ← hgl]
    have hconj : ((g * l₀ * g⁻¹ : stabSub W) : MulAut V) ∈ L₁ := by
      have hgG : (g : MulAut V) ∈ G := hA₁leG hgA
      have hmem := (Subgroup.mem_normalizer_iff.mp (hGnorm hgG) (l₀ : MulAut V)).mp hl₀
      simpa using hmem
    refine mem_autQuot.mpr ⟨g * l₀ * g⁻¹, hconj, ?_⟩
    simp [map_mul, map_inv]
  have hALbar : Abar ≤ Subgroup.normalizer (Lbar : Set (MulAut (V ⧸ W))) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · exact hALbar_one u hu l
    · intro hl
      have h := hALbar_one u⁻¹ (Abar.inv_mem hu) (u * l * u⁻¹) hl
      simpa [mul_assoc] using h
  have hACbar : Abar ⊓ Subgroup.centralizer (Lbar : Set (MulAut (V ⧸ W))) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxA, hxC⟩
    obtain ⟨g, hgA, hgx⟩ := mem_autQuot.mp hxA
    obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.mp hgA
    have hcomm : ∀ l : ↥L, (quotHom W g : MulAut (V ⧸ W)) * (θ l : MulAut (V ⧸ W)) =
        (θ l : MulAut (V ⧸ W)) * (quotHom W g : MulAut (V ⧸ W)) := by
      intro l
      have h := Subgroup.mem_centralizer_iff.mp hxC (θ l) (θ l).2
      rw [← hgx] at h
      exact h.symm
    have hu1 : u = 1 := by
      have huC : u ∈ A ⊓ Subgroup.centralizer (L : Set Q) :=
        ⟨hu, key u (hAL hu) g hgu hcomm⟩
      rw [hAC, Subgroup.mem_bot] at huC
      exact huC
    have hg1 : g = 1 := by
      apply Subtype.ext
      rw [← hgu, hu1, map_one]
      simp
    rw [← hgx, hg1, map_one]
  have hfixbar : fixV Lbar = ⊥ := fixV_autQuot_eq_bot hstabL₁ hfixW
  have hAQ : IsQuadratic A₁ := by
    rw [IsQuadratic, commV, Subgroup.closure_le]
    rintro w ⟨x, hx, v, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    refine (mem_fixV (X := A₁) (v := ρ a v * v⁻¹)).mpr ?_
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    exact hq a ha b' hb' v
  have hquadbar : IsQuadratic Abar := isQuadratic_autQuot hAQ W
  have hVquot : ∀ v : V ⧸ W, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, hV x]
      simp
  exact
    { W := W
      Lbar := Lbar
      Abar := Abar
      hstabA := hstabA
      hstabL := hstabL
      e := e
      eA := eA
      he := he
      heA := fun a => rfl
      hLbar := hLbar
      hZbar := hZbar
      hXbar := hXbar
      hALbar := hALbar
      hA4bar := hA4bar
      hA2bar := hA2bar
      hquadAbar := hquadbar
      hACbar := hACbar
      hfixLbar := hfixbar
      hVquot := hVquot
      key := key }

theorem inner_of_l2AutFacts_of_rep {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ρ : Q →* MulAut V) (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hL : IsSimpleGroup ↥L) (hZ : center ↥L = ⊥) (hX : L2AutFacts ↥L)
    (hAL : A ≤ normalizer (L : Set Q)) (hA4 : Nat.card A = 4) (hA2 : ∀ a ∈ A, a * a = 1)
    (hq : CFSG.LocalAnalysis.WeakClosure81.IsQuadraticOn ρ A)
    (hAC : A ⊓ centralizer (L : Set Q) = ⊥) :
    ∀ a ∈ A, ∃ l ∈ L, a * l⁻¹ ∈ centralizer (L : Set Q) := by
  classical
  let S := L2Setup.ofRep hV ρ hρ hL hZ hX hAL hA4 hA2 hq hAC
  intro a ha
  obtain ⟨lbar, hlbar, hcent⟩ :=
    inner_of_l2AutFacts S.hVquot S.hLbar S.hZbar S.hXbar S.hALbar S.hA4bar S.hA2bar
      S.hquadAbar S.hACbar S.hfixLbar (S.eA ⟨a, ha⟩) (S.eA ⟨a, ha⟩).2
  obtain ⟨l, hl⟩ := S.e.surjective ⟨lbar, hlbar⟩
  have hlval : (S.e l : MulAut (V ⧸ S.W)) = lbar := congrArg Subtype.val hl
  have hcent' : (S.eA ⟨a, ha⟩ : MulAut (V ⧸ S.W)) *
      ((S.e l : ↥S.Lbar) : MulAut (V ⧸ S.W))⁻¹ ∈
      Subgroup.centralizer (S.Lbar : Set (MulAut (V ⧸ S.W))) := by
    simpa [hlval] using hcent
  have hxnorm : a * (l : Q)⁻¹ ∈ Subgroup.normalizer (L : Set Q) :=
    (Subgroup.normalizer (L : Set Q)).mul_mem (hAL ha)
      ((Subgroup.normalizer (L : Set Q)).inv_mem (Subgroup.le_normalizer l.2))
  have hstab : ρ (a * (l : Q)⁻¹) ∈ stabSub S.W := by
    rw [map_mul, map_inv]
    exact (stabSub S.W).mul_mem (S.hstabA a ha) ((stabSub S.W).inv_mem (S.hstabL l.1 l.2))
  let g : stabSub S.W := ⟨ρ (a * (l : Q)⁻¹), hstab⟩
  have hcomm : ∀ l' : ↥L, (quotHom S.W g : MulAut (V ⧸ S.W)) *
      (S.e l' : MulAut (V ⧸ S.W)) =
      (S.e l' : MulAut (V ⧸ S.W)) * (quotHom S.W g : MulAut (V ⧸ S.W)) := by
    intro l'
    have hgl : (quotHom S.W g : MulAut (V ⧸ S.W)) =
        (S.eA ⟨a, ha⟩ : MulAut (V ⧸ S.W)) *
          ((S.e l : ↥S.Lbar) : MulAut (V ⧸ S.W))⁻¹ := by
      have hsplit : g = ⟨ρ a, S.hstabA a ha⟩ * ⟨ρ (l : Q), S.hstabL l.1 l.2⟩⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        simp [g, map_mul, map_inv]
      rw [hsplit, map_mul, map_inv, S.heA ⟨a, ha⟩, S.he l]
    rw [hgl]
    exact (Subgroup.mem_centralizer_iff.mp hcent' (S.e l') (S.e l').2).symm
  exact ⟨(l : Q), l.2, S.key (a * (l : Q)⁻¹) hxnorm g rfl hcomm⟩

theorem false_of_l2Facts_of_rep {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ρ : Q →* MulAut V) (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hL : IsSimpleGroup ↥L) (hZ : center ↥L = ⊥) (hX : L2AutFacts ↥L)
    (hI : L2InnerFacts ↥L) (hAL : A ≤ normalizer (L : Set Q)) (hA4 : Nat.card A = 4)
    (hA2 : ∀ a ∈ A, a * a = 1) (hq : CFSG.LocalAnalysis.WeakClosure81.IsQuadraticOn ρ A)
    (hAC : A ⊓ centralizer (L : Set Q) = ⊥) : False := by
  classical
  let S := L2Setup.ofRep hV ρ hρ hL hZ hX hAL hA4 hA2 hq hAC
  have hIbar : L2InnerFacts ↥S.Lbar := hI.of_mulEquiv S.e
  exact false_of_l2Facts S.hVquot S.hLbar S.hZbar S.hXbar hIbar S.hALbar S.hA4bar S.hA2bar
    S.hquadAbar S.hACbar S.hfixLbar

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
