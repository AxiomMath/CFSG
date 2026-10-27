module

public import CFSG.RankThree.PartTwo.Sec18.Item187F13Shape
public import CFSG.RankThree.PartTwo.Sec18.Item187F9Config
public import CFSG.RankThree.PartTwo.Sec18.Item187F11Act
public import CFSG.RankThree.PartTwo.Sec18.Item187F12Offender
import CFSG.RankThree.PartTwo.Sec18.SylowPlane

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise

private theorem map_mem_normalizer_map {Y Z : Type} [Group Y] [Group Z] (f : Y →* Z)
    {K : Subgroup Y} {g : Y} (hg : g ∈ Subgroup.normalizer (K : Set Y)) :
    f g ∈ Subgroup.normalizer ((K.map f : Subgroup Z) : Set Z) :=
  Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f hg)

private theorem mem_normalizer_subgroupOf_of {G : Type} [Group G] {Y K : Subgroup G}
    {x : ↥Y} (hx : (x : G) ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((K.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp hx (h : G)

private theorem commutatorElement_zpow_mem {Z : Type} [Group Z] {K : Subgroup Z} {g c : Z}
    (hc : c ∈ Subgroup.normalizer (K : Set Z)) (hg : g ∈ K) (n : ℤ) : ⁅g, c ^ n⁆ ∈ K := by
  have hn : c ^ n ∈ Subgroup.normalizer (K : Set Z) := zpow_mem hc n
  have heq : ⁅g, c ^ n⁆ = g * (c ^ n * g⁻¹ * (c ^ n)⁻¹) := by
    simp only [commutatorElement_def, mul_assoc]
  rw [heq]
  exact mul_mem hg ((Subgroup.mem_normalizer_iff.mp hn g⁻¹).mp (inv_mem hg))

section Certified


variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem MinCex.false_of_bad (h1812 : Item181_2) (h184 : Item184_1) (h186 : Item186H)
    (hX : MinCex A M H c X) (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X)
    (hbad : BadCase A M H X) : False := by
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hS
  set Y : Subgroup G := X ⊔ Subgroup.zpowers c with hY
  have hXY : X ≤ Y := le_sup_left
  have hcY : c ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hSX : S ≤ X := hX.pCoreOf_le
  set ψ := MinCex.psi hX with hψ
  set P : Subgroup (MulAut ↥(W1 X S)) := ((oTwoFive X).subgroupOf Y).map ψ with hP
  set S' : Subgroup (MulAut ↥(W1 X S)) := (S.subgroupOf Y).map ψ with hS'
  set Γ : Subgroup (MulAut ↥(W1 X S)) := (X.subgroupOf Y).map ψ with hΓ
  set c' : MulAut ↥(W1 X S) := ψ ⟨c, hcY⟩ with hc'
  obtain ⟨E₀, hE₀S, hE₀, hE₀C, hoff₀⟩ := MinCex.exists_offender h1812 h184 h186 hX hsol h5 hbad
  set E' : Subgroup (MulAut ↥(W1 X S)) := (E₀.subgroupOf Y).map ψ with hE'
  have hE₀comm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    (isElemTwo_of_isElemAbelian hE₀).1 x hx y hy
  have hE₀sq : ∀ x ∈ E₀, x * x = 1 := fun x hx => (isElemTwo_of_isElemAbelian hE₀).2 x hx
  have hE0Y : E₀ ≤ Y := (hE₀S.trans hSX).trans hXY
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hX.sec18H).1
  have hcSG : c ∈ Subgroup.normalizer (S : Set G) :=
    le_normalizer_pCoreOf hX.sec18H ((le_sup_left : A ≤ A ⊔ S) hcA)
  have hV : ∀ v : ↥(W1 X S), v * v = 1 := fun v => Subtype.ext (Sec3.mem_omegaG.mp v.2).2.2
  have hP5 : IsPGroup 5 P := MinCex.isPGroup_five_image h186 hX hsol h5
  have hS2 : IsPGroup 2 S' :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)).comap_subtype).map ψ
  have hΓeq : P ⊔ S' = Γ := (MinCex.image_eq h186 hX hsol h5 ψ).symm
  have hPΓ : P ≤ Γ := le_sup_left.trans hΓeq.le
  have hSΓ : S' ≤ Γ := le_sup_right.trans hΓeq.le
  have hΓP : Γ ≤ Subgroup.normalizer (P : Set (MulAut ↥(W1 X S))) := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    have hxN : (x : G) ∈ Subgroup.normalizer (oTwoFive X : Set G) :=
      normalizer_le_normalizer_oTwoFive X (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp hx))
    exact map_mem_normalizer_map (K := (oTwoFive X).subgroupOf Y) ψ
      (mem_normalizer_subgroupOf_of (x := x) hxN)
  have hSP : S' ≤ Subgroup.normalizer (P : Set (MulAut ↥(W1 X S))) := hSΓ.trans hΓP
  have hcP : c' ∈ Subgroup.normalizer (P : Set (MulAut ↥(W1 X S))) :=
    map_mem_normalizer_map (K := (oTwoFive X).subgroupOf Y) (g := ⟨c, hcY⟩) ψ
      (mem_normalizer_subgroupOf_of (x := (⟨c, hcY⟩ : ↥Y)) (MinCex.A_le_normalizer_oTwoFive hX hcA))
  have hcS : c' ∈ Subgroup.normalizer (S' : Set (MulAut ↥(W1 X S))) :=
    map_mem_normalizer_map (K := S.subgroupOf Y) (g := ⟨c, hcY⟩) ψ
      (mem_normalizer_subgroupOf_of (x := (⟨c, hcY⟩ : ↥Y)) hcSG)
  have hc3 : c' ^ 3 = 1 := by
    have h3 : c ^ 3 = 1 := by
      have := pow_orderOf_eq_one c
      rwa [MinCex.orderOf_c h184 hX] at this
    have hY3 : (⟨c, hcY⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [hc', ← map_pow, hY3, map_one]
  have hfaith : ∀ s ∈ S', (∀ p ∈ P, s * p = p * s) → s = 1 :=
    inf_centralizer_eq_bot_of_O2 hP5 hS2 hPΓ hSΓ hΓeq hΓP
      (fun N hNΓ hn hN2 => MinCex.image_O2_trivial h186 hX hsol h5 hbad N hNΓ hn hN2)
  have hk : ψ.ker = (Subgroup.centralizer (W1 X S : Set G)).subgroupOf Y :=
    ker_actOn (W1 X S) Y (MinCex.sup_zpowers_le_normalizer_W1 hX)
  have hC : ∀ s : G, s ∈ S →
      (s ∈ Subgroup.centralizer (W1 X S : Set G) ↔ s ∈ CFSG.Open.pCoreOf 2 X) := by
    intro s hsS
    constructor
    · intro hsC
      have hXC : s ∈ X ⊓ Subgroup.centralizer (W1 X S : Set G) :=
        Subgroup.mem_inf.mpr ⟨hSX hsS, hsC⟩
      rw [MinCex.centralizer_W1 h186 hX hbad] at hXC
      have h2 : s ∈ (X ⊓ Subgroup.centralizer (Wsub X S : Set G)) ⊓ S :=
        Subgroup.mem_inf.mpr ⟨hXC, hsS⟩
      rwa [MinCex.inf_centralizer_Wsub_inf_S h186 hX hbad] at h2
    · intro hsQ
      have h2 : s ∈ (X ⊓ Subgroup.centralizer (Wsub X S : Set G)) ⊓ S := by
        rw [MinCex.inf_centralizer_Wsub_inf_S h186 hX hbad]
        exact hsQ
      have hCW : Subgroup.centralizer (Wsub X S : Set G) ≤
          Subgroup.centralizer (W1 X S : Set G) :=
        Subgroup.centralizer_le (fun w hw => Sec3.omegaG_le _ hw)
      exact hCW (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h2).1).2
  have hker : ∀ s : ↥Y, s ∈ S.subgroupOf Y →
      (ψ s = 1 ↔ s ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf Y) := by
    intro s hs
    rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hC s (Subgroup.mem_subgroupOf.mp hs)
  have hshape : Shape81 S' c' := MinCex.shape81_map h1812 h184 h186 hX hsol h5 ψ hker
  have hperf : (IsCyclic S' ∧ ∀ s ∈ S', c' * s * c'⁻¹ = s) → ⁅P, Subgroup.zpowers c'⁆ = P := by
    rintro ⟨-, hcyc⟩
    have hcent : ⁅S, Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 X := by
      refine Subgroup.commutator_le.mpr fun x hx k hk' => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk'
      have hxY : x ∈ Y := hXY (hSX hx)
      have hxS : (⟨x, hxY⟩ : ↥Y) ∈ S.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx
      have hcomm : Commute c' (ψ ⟨x, hxY⟩) := by
        have h := hcyc (ψ ⟨x, hxY⟩) (Subgroup.mem_map_of_mem ψ hxS)
        exact mul_inv_eq_iff_eq_mul.mp h
      have hcn : Commute (ψ ⟨x, hxY⟩) (c' ^ n) := (hcomm.zpow_left n).symm
      have hψz : ψ ⁅(⟨x, hxY⟩ : ↥Y), (⟨c, hcY⟩ : ↥Y) ^ n⁆ = 1 := by
        rw [map_commutatorElement, map_zpow]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcn.eq
      have hzS : ⁅(⟨x, hxY⟩ : ↥Y), (⟨c, hcY⟩ : ↥Y) ^ n⁆ ∈ S.subgroupOf Y :=
        Subgroup.mem_subgroupOf.mpr (commutatorElement_zpow_mem hcSG hx n)
      exact Subgroup.mem_subgroupOf.mp ((hker _ hzS).mp hψz)
    have hsub := MinCex.oTwoFive_le_commutator_sup h1812 h184 h186 hX hsol h5 hcent
    apply le_antisymm
    · refine Subgroup.commutator_le.mpr fun g hg k hk' => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk'
      exact commutatorElement_zpow_mem hcP hg n
    · have hPle : oTwoFive X ≤
          (((⁅P, Subgroup.zpowers c'⁆ : Subgroup (MulAut ↥(W1 X S))).comap ψ).map Y.subtype) := by
        refine hsub.trans (sup_le ?_ ?_)
        · refine Subgroup.commutator_le.mpr fun x hx k hk' => ?_
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk'
          have hxY : x ∈ Y := hXY (oTwoFive_le X hx)
          refine Subgroup.mem_map.mpr ⟨⁅(⟨x, hxY⟩ : ↥Y), (⟨c, hcY⟩ : ↥Y) ^ n⁆, ?_, rfl⟩
          rw [Subgroup.mem_comap, map_commutatorElement, map_zpow]
          exact Subgroup.commutator_mem_commutator
            (Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr hx))
            (Subgroup.zpow_mem_zpowers c' n)
        · intro q hq
          have hqS : q ∈ S := pCoreOf_le_S h186 hX hq
          have hqY : q ∈ Y := hXY (CFSG.LieType.BorelTits.pCoreOf_le 2 X hq)
          have hψq : ψ ⟨q, hqY⟩ = 1 :=
            (hker ⟨q, hqY⟩ (Subgroup.mem_subgroupOf.mpr hqS)).mpr (Subgroup.mem_subgroupOf.mpr hq)
          refine Subgroup.mem_map.mpr ⟨⟨q, hqY⟩, ?_, rfl⟩
          rw [Subgroup.mem_comap, hψq]
          exact one_mem _
      intro p hp
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hp
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hPle (Subgroup.mem_subgroupOf.mp hy))
      have hzy' : z = y := Subtype.ext hzy
      rw [← hzy']
      exact Subgroup.mem_comap.mp hz
  have hES : E' ≤ S' := Subgroup.map_mono fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hE₀S (Subgroup.mem_subgroupOf.mp hy))
  have hEab : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE₀comm _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
  have hE2 : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul]
    have h2 : a * a = 1 :=
      Subtype.ext (by
        rw [Subgroup.coe_mul, hE₀sq _ (Subgroup.mem_subgroupOf.mp ha), Subgroup.coe_one])
    rw [h2, map_one]
  have hE1 : E' ≠ ⊥ := by
    intro hbot
    apply hE₀C
    intro e he
    have heY : e ∈ Y := hXY (hSX (hE₀S he))
    have hmem : ψ ⟨e, heY⟩ ∈ E' :=
      Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr he)
    rw [hbot] at hmem
    have hψe : ψ ⟨e, heY⟩ = 1 := Subgroup.mem_bot.mp hmem
    have hC1 : e ∈ Subgroup.centralizer (W1 X S : Set G) := by
      have hmk : (⟨e, heY⟩ : ↥Y) ∈ ψ.ker := MonoidHom.mem_ker.mpr hψe
      rw [hk, Subgroup.mem_subgroupOf] at hmk
      exact hmk
    have hX1 : e ∈ X ⊓ Subgroup.centralizer (W1 X S : Set G) :=
      Subgroup.mem_inf.mpr ⟨hSX (hE₀S he), hC1⟩
    rw [MinCex.centralizer_W1 h186 hX hbad] at hX1
    exact hX1
  set f : ↥E₀ →* MulAut ↥(W1 X S) := ψ.comp (Subgroup.inclusion hE0Y) with hf
  have hfker : f.ker = (E₀ ⊓ Subgroup.centralizer (Wsub X S : Set G)).subgroupOf E₀ := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hmem : (Subgroup.inclusion hE0Y e : ↥Y) ∈ ψ.ker := MonoidHom.mem_ker.mpr h
      rw [hk, Subgroup.mem_subgroupOf] at hmem
      have hXC : (e : G) ∈ X ⊓ Subgroup.centralizer (W1 X S : Set G) :=
        Subgroup.mem_inf.mpr ⟨hSX (hE₀S e.2), hmem⟩
      rw [MinCex.centralizer_W1 h186 hX hbad] at hXC
      exact Subgroup.mem_inf.mpr ⟨e.2, (Subgroup.mem_inf.mp hXC).2⟩
    · intro h
      have hC1 : (e : G) ∈ Subgroup.centralizer (W1 X S : Set G) := by
        have hXC : (e : G) ∈ X ⊓ Subgroup.centralizer (Wsub X S : Set G) :=
          Subgroup.mem_inf.mpr ⟨hSX (hE₀S e.2), (Subgroup.mem_inf.mp h).2⟩
        rw [← MinCex.centralizer_W1 h186 hX hbad] at hXC
        exact (Subgroup.mem_inf.mp hXC).2
      have hmem : (Subgroup.inclusion hE0Y e : ↥Y) ∈ ψ.ker := by
        rw [hk, Subgroup.mem_subgroupOf]
        exact hC1
      exact MonoidHom.mem_ker.mp hmem
  have hfrange : f.range = E' := by
    ext x
    constructor
    · intro hx
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hx
      exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr e.2)
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact MonoidHom.mem_range.mpr ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have hEcard : Nat.card (↥E₀ ⧸ (E₀ ⊓ Subgroup.centralizer (Wsub X S : Set G)).subgroupOf E₀) =
      Nat.card E' := by
    rw [← hfker, ← hfrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hoff : (Fix E').index ≤ 2 * Nat.card E' := by
    have hFix : Nat.card ↥(Fix E') =
        Nat.card ↥(W1 X S ⊓ Subgroup.centralizer (E₀ : Set G)) :=
      card_Fix_actOn (W1 X S) (X ⊔ Subgroup.zpowers c) (MinCex.sup_zpowers_le_normalizer_W1 hX)
        hE0Y
    have hmul : Nat.card ↥(Fix E') * (Fix E').index = Nat.card ↥(W1 X S) :=
      Subgroup.card_mul_index (H := Fix E')
    rw [hEcard] at hoff₀
    have hpos : 0 < Nat.card ↥(W1 X S ⊓ Subgroup.centralizer (E₀ : Set G)) := Nat.card_pos
    have key : Nat.card ↥(W1 X S ⊓ Subgroup.centralizer (E₀ : Set G)) * (Fix E').index =
        Nat.card ↥(W1 X S) := by
      rw [← hFix]
      exact hmul
    have key2 : Nat.card ↥(W1 X S ⊓ Subgroup.centralizer (E₀ : Set G)) * (Fix E').index ≤
        Nat.card ↥(W1 X S ⊓ Subgroup.centralizer (E₀ : Set G)) * (2 * Nat.card E') := by
      rw [key]
      calc Nat.card ↥(W1 X S) ≤ 2 * Nat.card E' * Nat.card ↥(W1 X S ⊓ Subgroup.centralizer (E₀ : Set G)) :=
            hoff₀
        _ = Nat.card ↥(W1 X S ⊓ Subgroup.centralizer (E₀ : Set G)) * (2 * Nat.card E') := by ring
    exact Nat.le_of_mul_le_mul_left key2 hpos
  exact bad_config_false hV P S' E' c' hP5 hS2 hSP hcP hcS hc3 hfaith hshape hperf hES hEab hE2
    hE1 hoff

end Certified

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
