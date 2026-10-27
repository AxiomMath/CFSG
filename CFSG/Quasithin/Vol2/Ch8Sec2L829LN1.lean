module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Sections

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

private theorem cf_of_cover {X Y : Type} [Group X] [Group Y] (f : X →* Y) {L : Type} [Group L]
    (N M : Subgroup Y) (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal)
    (hNs : N.IsSubnormal) (hMs : M.IsSubnormal)
    (hs : IsSimpleGroup (M ⧸ N.subgroupOf M)) (e : (M ⧸ N.subgroupOf M) ≃* L)
    (hcov : ∀ m ∈ M, ∃ x : X, ∃ n ∈ N, f x * n = m) : E1.IsCompositionFactor X L := by
  haveI := hN
  haveI := hs
  let g : ↥(M.comap f) →* ↥M :=
    (f.comp (M.comap f).subtype).codRestrict M (fun x => Subgroup.mem_comap.mp x.2)
  let Φ : ↥(M.comap f) →* ↥M ⧸ N.subgroupOf M := (QuotientGroup.mk' (N.subgroupOf M)).comp g
  have hΦ : ∀ x : ↥(M.comap f), Φ x = ((g x : ↥M) : ↥M ⧸ N.subgroupOf M) := fun x => rfl
  have hker : Φ.ker = (N.comap f).subgroupOf (M.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, hΦ, QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (N.subgroupOf M) q
    subst hm
    obtain ⟨x, n, hn, hxn⟩ := hcov m.1 m.2
    have hfx : x ∈ M.comap f := by
      rw [Subgroup.mem_comap]
      have hfx' : f x = m.1 * n⁻¹ := by rw [← hxn]; group
      rw [hfx']
      exact M.mul_mem m.2 (M.inv_mem (hNM hn))
    refine ⟨⟨x, hfx⟩, ?_⟩
    have key : ((g ⟨x, hfx⟩)⁻¹ * m : ↥M).1 = n := by
      show (f x)⁻¹ * m.1 = n
      rw [← hxn]
      group
    rw [hΦ, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf, key]
    exact hn
  haveI hKn : ((N.comap f).subgroupOf (M.comap f)).Normal := by
    rw [← hker]
    infer_instance
  let Ψ : (↥(M.comap f) ⧸ (N.comap f).subgroupOf (M.comap f)) ≃* (↥M ⧸ N.subgroupOf M) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj)
  unfold E1.IsCompositionFactor
  exact ⟨N.comap f, M.comap f, hKn, Subgroup.comap_mono hNM, hNs.comap f, hMs.comap f,
    Ψ.isSimpleGroup, ⟨Ψ.trans e⟩⟩

private theorem normal_map_subgroupOf_aux {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (M N : Subgroup X) (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal) :
    ((N.map f).subgroupOf (M.map f)).Normal := by
  constructor
  intro n hn g
  obtain ⟨m, hm, hmg⟩ := Subgroup.mem_map.mp g.2
  obtain ⟨k, hk, hkn⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
  have hkm : m * k * m⁻¹ ∈ N := by
    have h1 := hN.conj_mem ⟨k, hNM hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨m, hm⟩
    exact Subgroup.mem_subgroupOf.mp h1
  have e : ((g * n * g⁻¹ : ↥(M.map f)) : Y) = f (m * k * m⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hmg, hkn]
  rw [Subgroup.mem_subgroupOf, e]
  exact Subgroup.mem_map_of_mem f hkm

private theorem cf_push {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) {L : Type} [Group L] (N M : Subgroup X) (hNM : N ≤ M)
    (hN : (N.subgroupOf M).Normal) (hNs : N.IsSubnormal) (hMs : M.IsSubnormal)
    (hs : IsSimpleGroup (M ⧸ N.subgroupOf M)) (e : (M ⧸ N.subgroupOf M) ≃* L)
    (hker : ∀ m ∈ M, f m ∈ N.map f → m ∈ N) : E1.IsCompositionFactor Y L := by
  haveI := hN
  haveI := hs
  have hnorm : ((N.map f).subgroupOf (M.map f)).Normal :=
    normal_map_subgroupOf_aux f M N hNM hN
  haveI := hnorm
  let g : ↥M →* ↥(M.map f) :=
    (f.comp M.subtype).codRestrict (M.map f) (fun m => Subgroup.mem_map_of_mem f m.2)
  let Θ : ↥M →* ↥(M.map f) ⧸ (N.map f).subgroupOf (M.map f) :=
    (QuotientGroup.mk' ((N.map f).subgroupOf (M.map f))).comp g
  have hΘsurj : Function.Surjective Θ := by
    intro q
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective ((N.map f).subgroupOf (M.map f)) q
    obtain ⟨m, hm, hfm⟩ := Subgroup.mem_map.mp y.2
    refine ⟨⟨m, hm⟩, ?_⟩
    have hgm : g ⟨m, hm⟩ = y := Subtype.ext hfm
    rw [← hy]
    show QuotientGroup.mk' _ (g ⟨m, hm⟩) = QuotientGroup.mk' _ y
    rw [hgm]
  have hΘker : Θ.ker = N.subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' _ (g x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      exact hker x.1 x.2 h1
    · intro h1
      exact Subgroup.mem_map_of_mem f h1
  let Ψ : (↥M ⧸ N.subgroupOf M) ≃* (↥(M.map f) ⧸ (N.map f).subgroupOf (M.map f)) :=
    (QuotientGroup.quotientMulEquivOfEq hΘker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hΘsurj)
  have hsimp : IsSimpleGroup (↥(M.map f) ⧸ (N.map f).subgroupOf (M.map f)) :=
    Ψ.symm.isSimpleGroup
  unfold E1.IsCompositionFactor
  exact ⟨N.map f, M.map f, hnorm, Subgroup.map_mono hNM, hNs.map hf, hMs.map hf, hsimp,
    ⟨Ψ.symm.trans e⟩⟩

theorem isCompositionFactor_of_surjective {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) {L : Type} [Group L]
    (h : E1.IsCompositionFactor Y L) : E1.IsCompositionFactor X L := by
  obtain ⟨N, M, hN, hNM, hNs, hMs, hs, ⟨e⟩⟩ := h
  refine cf_of_cover f N M hNM hN hNs hMs hs e (fun m _ => ?_)
  obtain ⟨x, hx⟩ := hf m
  exact ⟨x, 1, N.one_mem, by rw [mul_one, hx]⟩

theorem isCompositionFactor_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {L : Type}
    [Group L] : E1.IsCompositionFactor X L ↔ E1.IsCompositionFactor Y L :=
  ⟨isCompositionFactor_of_surjective e.symm.toMonoidHom e.symm.surjective,
    isCompositionFactor_of_surjective e.toMonoidHom e.surjective⟩

theorem isCompositionFactor_of_subnormal_surjection {X : Type} [Group X] {A : Subgroup X}
    (hA : A.IsSubnormal) {L : Type} [Group L] (hL : IsSimpleGroup L) (ψ : ↥A →* L)
    (hψ : Function.Surjective ψ) : E1.IsCompositionFactor X L := by
  haveI := hL
  have hkey : (ψ.ker.map A.subtype).subgroupOf A = ψ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hxy : y = x := Subtype.ext hyx
      exact hxy ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  haveI hkn : ((ψ.ker.map A.subtype).subgroupOf A).Normal := by
    rw [hkey]
    infer_instance
  have hNA : ψ.ker.map A.subtype ≤ A := Subgroup.map_subtype_le ψ.ker
  have hNs : (ψ.ker.map A.subtype).IsSubnormal := by
    refine Subgroup.IsSubnormal.trans hNA ?_ hA
    rw [hkey]
    exact Subgroup.Normal.isSubnormal inferInstance
  let Ψ : (↥A ⧸ (ψ.ker.map A.subtype).subgroupOf A) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hkey).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  unfold E1.IsCompositionFactor
  exact ⟨ψ.ker.map A.subtype, A, hkn, hNA, hNs, hA, Ψ.isSimpleGroup, ⟨Ψ⟩⟩

private theorem not_cf_of_subsingleton {X : Type} [Group X] (hX : ∀ x : X, x = 1) {L : Type}
    [Group L] (h : E1.IsCompositionFactor X L) : False := by
  obtain ⟨N, M, hN, hNM, hNs, hMs, hs, ⟨e⟩⟩ := h
  haveI := hs
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥M ⧸ N.subgroupOf M)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (N.subgroupOf M) a
  subst hx
  apply ha
  have hx1 : x = 1 := Subtype.ext (hX x.1)
  rw [hx1]
  exact map_one (QuotientGroup.mk' (N.subgroupOf M))

theorem isCompositionFactor_of_sup_eq_top {X : Type} [Group X] (A B : Subgroup X) [A.Normal]
    [B.Normal] (hAB : A ⊔ B = ⊤) {L : Type} [Group L] (h : E1.IsCompositionFactor X L) :
    E1.IsCompositionFactor ↥A L ∨ E1.IsCompositionFactor ↥B L := by
  classical
  obtain ⟨N, M, hN, hNM, hNs, hMs, hs, ⟨e⟩⟩ := h
  haveI := hs
  by_cases hK : (M ⊓ A) ⊔ N = M
  ·
    left
    have hLE : M ⊓ A ≤ Subgroup.normalizer (N : Set X) := fun x hx =>
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hN (Subgroup.mem_inf.mp hx).1
    refine cf_of_cover A.subtype N M hNM hN hNs hMs hs e ?_
    intro m hm
    have hm' : m ∈ ((M ⊓ A : Subgroup X) : Set X) * (N : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (M ⊓ A) N hLE, hK]
      exact hm
    obtain ⟨a, ha, n, hn, han⟩ := Set.mem_mul.mp hm'
    exact ⟨⟨a, (Subgroup.mem_inf.mp ha).2⟩, n, hn, han⟩
  ·
    right
    have hle : M ⊓ A ≤ N := by
      haveI : ((A.subgroupOf M ⊔ N.subgroupOf M).map
          (QuotientGroup.mk' (N.subgroupOf M))).Normal :=
        Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
      rcases Subgroup.Normal.eq_bot_or_eq_top
          ((A.subgroupOf M ⊔ N.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) with
        hS | hS
      · intro x hx
        have h1 : ((⟨x, (Subgroup.mem_inf.mp hx).1⟩ : ↥M) : ↥M ⧸ N.subgroupOf M) ∈
            (A.subgroupOf M ⊔ N.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)) :=
          Subgroup.mem_map_of_mem _
            (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hx).2))
        rw [hS, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
        exact Subgroup.mem_subgroupOf.mp h1
      · exfalso
        apply hK
        have htop : ∀ y : ↥M, y ∈ A.subgroupOf M ⊔ N.subgroupOf M := by
          intro y
          have h1 : QuotientGroup.mk' (N.subgroupOf M) y ∈
              (A.subgroupOf M ⊔ N.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)) := by
            rw [hS]
            exact Subgroup.mem_top _
          obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp h1
          obtain ⟨z, hz, hkz⟩ := (QuotientGroup.mk'_eq_mk' (N.subgroupOf M)).mp hky
          rw [← hkz]
          exact Subgroup.mul_mem _ hk (Subgroup.mem_sup_right hz)
        refine le_antisymm (sup_le inf_le_left hNM) (fun m hm => ?_)
        obtain ⟨a, ha, q, hq, haq⟩ :=
          Subgroup.mem_sup_of_normal_right.mp (htop ⟨m, hm⟩)
        have hm_eq : m = (a : X) * (q : X) := (congrArg Subtype.val haq).symm
        rw [hm_eq]
        exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨a.2, Subgroup.mem_subgroupOf.mp ha⟩)
          (Subgroup.mem_subgroupOf.mp hq)
    have hker : ∀ m ∈ M, (QuotientGroup.mk' A) m ∈ N.map (QuotientGroup.mk' A) → m ∈ N := by
      intro m hm hmN
      obtain ⟨n, hn, hnm⟩ := Subgroup.mem_map.mp hmN
      obtain ⟨z, hz, hnz⟩ := (QuotientGroup.mk'_eq_mk' A).mp hnm
      have hzM : z ∈ M := by
        have hz' : z = n⁻¹ * m := by
          rw [← hnz]
          group
        rw [hz']
        exact M.mul_mem (M.inv_mem (hNM hn)) hm
      have hzN : z ∈ N := hle (Subgroup.mem_inf.mpr ⟨hzM, hz⟩)
      rw [← hnz]
      exact N.mul_mem hn hzN
    have hCF : E1.IsCompositionFactor (X ⧸ A) L :=
      cf_push (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A) N M hNM hN hNs hMs hs e hker
    have hsurjB : Function.Surjective ((QuotientGroup.mk' A).comp B.subtype) := by
      intro y
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective A y
      have hxAB : x ∈ A ⊔ B := by
        rw [hAB]
        exact Subgroup.mem_top x
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hxAB
      refine ⟨⟨b, hb⟩, ?_⟩
      have ha1 : QuotientGroup.mk' A a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
      rw [← hx, ← hab]
      show QuotientGroup.mk' A b = QuotientGroup.mk' A (a * b)
      rw [map_mul, ha1, one_mul]
    exact isCompositionFactor_of_surjective _ hsurjB hCF

private theorem sup_subgroupOf_finset_aux {X : Type} [Group X] (B : Subgroup X)
    (𝒮 : Finset (Subgroup X)) (h : ∀ N ∈ 𝒮, N ≤ B) :
    (𝒮.sup fun N => N.subgroupOf B) = (𝒮.sup id).subgroupOf B := by
  classical
  induction 𝒮 using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ N ∈ s, N ≤ B := fun N hN => h N (Finset.mem_insert_of_mem hN)
    have ha' : a ≤ B := h a (Finset.mem_insert_self a s)
    simp only [Finset.sup_insert, id_eq]
    rw [ih hs, Subgroup.subgroupOf_sup ha' (Finset.sup_le (f := id) hs)]

private theorem normal_finset_sup_aux {X : Type} [Group X] (𝒮 : Finset (Subgroup X))
    (h : ∀ N ∈ 𝒮, N.Normal) : (𝒮.sup id).Normal := by
  classical
  induction 𝒮 using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty]
    infer_instance
  | insert a s ha ih =>
    have ha' : a.Normal := h a (Finset.mem_insert_self a s)
    have hs : ∀ N ∈ s, N.Normal := fun N hN => h N (Finset.mem_insert_of_mem hN)
    haveI := ih hs
    simp only [Finset.sup_insert, id_eq]
    exact Subgroup.sup_normal a (s.sup id)

private theorem not_cf_of_sup_empty {X : Type} [Group X]
    (hsup : (∅ : Finset (Subgroup X)).sup id = ⊤) {L : Type} [Group L]
    (hcf : E1.IsCompositionFactor X L) : False := by
  have htriv : ∀ x : X, x = 1 := by
    intro x
    have hx := Subgroup.mem_top x
    rw [← hsup] at hx
    simpa using hx
  exact not_cf_of_subsingleton htriv hcf

private theorem finset_sup_cf_aux (n : ℕ) :
    ∀ {X : Type} [Group X] (𝒩 : Finset (Subgroup X)), 𝒩.card ≤ n →
      (∀ N ∈ 𝒩, N.Normal) → 𝒩.sup id = ⊤ →
      ∀ {L : Type} [Group L], E1.IsCompositionFactor X L →
        ∃ N ∈ 𝒩, E1.IsCompositionFactor ↥N L := by
  classical
  induction n with
  | zero =>
    intro X _ 𝒩 hcard _ hsup L _ hcf
    have hempty : 𝒩 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hempty
    exact (not_cf_of_sup_empty hsup hcf).elim
  | succ n ih =>
    intro X _ 𝒩 hcard hN hsup L _ hcf
    by_cases hne : 𝒩.Nonempty
    · obtain ⟨N₀, hN₀⟩ := hne
      haveI : N₀.Normal := hN N₀ hN₀
      have hsplit : 𝒩 = insert N₀ (𝒩.erase N₀) := (Finset.insert_erase hN₀).symm
      have hsup2 : N₀ ⊔ (𝒩.erase N₀).sup id = ⊤ := by
        rw [hsplit, Finset.sup_insert] at hsup
        exact hsup
      haveI : ((𝒩.erase N₀).sup id).Normal :=
        normal_finset_sup_aux (𝒩.erase N₀) (fun N hN' => hN N (Finset.mem_of_mem_erase hN'))
      rcases isCompositionFactor_of_sup_eq_top N₀ ((𝒩.erase N₀).sup id) hsup2 hcf with
        h₀ | hB
      · exact ⟨N₀, hN₀, h₀⟩
      · have hsubB : ∀ N ∈ 𝒩.erase N₀, N ≤ (𝒩.erase N₀).sup id :=
          fun N hN' => Finset.le_sup (f := id) hN'
        have hcard' : ((𝒩.erase N₀).image
            (fun N => N.subgroupOf ((𝒩.erase N₀).sup id))).card ≤ n := by
          have h1 := Finset.card_image_le (s := 𝒩.erase N₀)
            (f := fun N => N.subgroupOf ((𝒩.erase N₀).sup id))
          have h2 := Finset.card_erase_of_mem hN₀
          omega
        have hnorm' : ∀ T ∈ (𝒩.erase N₀).image
            (fun N => N.subgroupOf ((𝒩.erase N₀).sup id)), T.Normal := by
          intro T hT
          obtain ⟨N, hN', rfl⟩ := Finset.mem_image.mp hT
          haveI := hN N (Finset.mem_of_mem_erase hN')
          infer_instance
        have hsup' : ((𝒩.erase N₀).image
            (fun N => N.subgroupOf ((𝒩.erase N₀).sup id))).sup id = ⊤ := by
          rw [Finset.sup_image]
          change (𝒩.erase N₀).sup (fun N => N.subgroupOf ((𝒩.erase N₀).sup id)) = ⊤
          rw [sup_subgroupOf_finset_aux _ (𝒩.erase N₀) hsubB, Subgroup.subgroupOf_self]
        obtain ⟨T, hT, hTcf⟩ := ih _ hcard' hnorm' hsup' hB
        obtain ⟨N, hN', rfl⟩ := Finset.mem_image.mp hT
        exact ⟨N, Finset.mem_of_mem_erase hN',
          (isCompositionFactor_congr (Subgroup.subgroupOfEquivOfLe (hsubB N hN'))).mp hTcf⟩
    · have hempty : 𝒩 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hempty
      exact (not_cf_of_sup_empty hsup hcf).elim

theorem isCompositionFactor_of_finset_sup {X : Type} [Group X] (𝒩 : Finset (Subgroup X))
    (hN : ∀ N ∈ 𝒩, N.Normal) (hsup : 𝒩.sup id = ⊤) {L : Type} [Group L]
    (h : E1.IsCompositionFactor X L) : ∃ N ∈ 𝒩, E1.IsCompositionFactor ↥N L :=
  finset_sup_cf_aux 𝒩.card 𝒩 le_rfl hN hsup h

end CFSG.Quasithin.H13.L829N
