module

public import CFSG.Quasithin.EmptyFaithful.S146yCom
public import CFSG.Quasithin.EmptyFaithful.S146F23

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section KM

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.kMoves_normal (hgen : A6CoverGen) (S : Setting146 G T M) {K U₁ U₂ : Subgroup G}
    {s u : G} (hK : K ∈ cComp (mcOf T)) (hdec : IsDecompUK T M K U₁ U₂ s)
    (hKn : mcOf T ≤ Subgroup.normalizer (K : Set G)) (huU : u ∈ U₁)
    (hunc : ¬ ⁅Subgroup.zpowers u, K⁆ ≤ Zz)
    (hN : T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u) :
    (∃ x ∈ K, x * u * x⁻¹ ≠ u) ∧
      ∀ t ∈ T, t ∉ tZero T u → ∃ x ∈ K, x * (u * (t * u * t⁻¹)) * x⁻¹ ≠ u * (t * u * t⁻¹) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  have hU₁U := (le_U_of_decomp hK hdec).1
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (hU₁U huU)
  have hKU₁ := S.le_normalizer_U₁_of_decomp hK hdec
  have hUc : ∀ {x y : G}, x ∈ uOfL22 T M → y ∈ uOfL22 T M → x * y = y * x := fun hx hy =>
    S.comm_of_mem_conjClosure hx hy
  have hnc : ∃ x ∈ K, x * u * x⁻¹ * u⁻¹ ∉ Zz := by
    by_contra hcon
    push Not at hcon
    exact hunc (commutator_zpowers_le_of_forall (fun k hk => S.normalizer_Z.ge (hKG hk))
      (fun z hz => S146T.comm_Z huG hz) hcon)
  have part1 : ∃ x ∈ K, x * u * x⁻¹ ≠ u := by
    obtain ⟨x, hx, hxn⟩ := hnc
    refine ⟨x, hx, fun h => hxn ?_⟩
    rw [h, mul_inv_cancel]
    exact Subgroup.one_mem _
  refine ⟨part1, ?_⟩
  intro t htT htn
  by_contra hcon
  push Not at hcon
  have htU : t ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ (hTH htT)
  have hutU : t * u * t⁻¹ ∈ uOfL22 T M := (Subgroup.mem_normalizer_iff.mp htU u).mp (hU₁U huU)
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hKn (hTH htT)
  have htZ : t ∈ Subgroup.normalizer (Zz : Set G) := S.normalizer_Z.ge (hTH htT)
  have htnU : t ∉ Subgroup.normalizer (U₁ : Set G) := fun h => htn (hN ⟨htT, h⟩)
  have hKU₁t : K ≤ Subgroup.normalizer (conjSub t U₁ : Set G) := le_normalizer_conjSub htK hKU₁
  set W : Subgroup G := U₁ ⊓ conjSub t U₁ with hWdef
  have hZW : Zz ≤ W := by
    intro z hz
    refine ⟨hdec.Z₁ hz, mem_conjSub.mpr ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htZ) z).mp hz
    simpa using hdec.Z₁ this
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKU₁ hk, hKU₁t hk⟩
  have hcomm : ∀ x ∈ K, x * u * x⁻¹ * u⁻¹ ∈ W := by
    intro x hx
    have hxuU : x * u * x⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ (hKG hx)) u).mp (hU₁U huU)
    have hxcU : x * (t * u * t⁻¹) * x⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ (hKG hx)) _).mp hutU
    have h1 : x * u * x⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp (hKU₁ hx) u).mp huU
    have h2 : t * u * t⁻¹ ∈ conjSub t U₁ := mul_mem_conjSub huU
    have h3 : x * (t * u * t⁻¹) * x⁻¹ ∈ conjSub t U₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKU₁t hx) _).mp h2
    have hab := hcon x hx
    have hab' : (x * u * x⁻¹) * (x * (t * u * t⁻¹) * x⁻¹) = u * (t * u * t⁻¹) := by
      rw [← hab]; group
    have ha : x * u * x⁻¹ = u * (t * u * t⁻¹) * (x * (t * u * t⁻¹) * x⁻¹)⁻¹ :=
      eq_mul_inv_of_mul_eq hab'
    have hcb : u * ((t * u * t⁻¹) * (x * (t * u * t⁻¹) * x⁻¹)⁻¹) =
        ((t * u * t⁻¹) * (x * (t * u * t⁻¹) * x⁻¹)⁻¹) * u :=
      hUc (hU₁U huU) ((uOfL22 T M).mul_mem hutU ((uOfL22 T M).inv_mem hxcU))
    have e : x * u * x⁻¹ * u⁻¹ = (t * u * t⁻¹) * (x * (t * u * t⁻¹) * x⁻¹)⁻¹ := by
      calc x * u * x⁻¹ * u⁻¹
          = (u * (t * u * t⁻¹) * (x * (t * u * t⁻¹) * x⁻¹)⁻¹) * u⁻¹ := by rw [← ha]
        _ = (u * ((t * u * t⁻¹) * (x * (t * u * t⁻¹) * x⁻¹)⁻¹)) * u⁻¹ := by group
        _ = (((t * u * t⁻¹) * (x * (t * u * t⁻¹) * x⁻¹)⁻¹) * u) * u⁻¹ := by rw [hcb]
        _ = (t * u * t⁻¹) * (x * (t * u * t⁻¹) * x⁻¹)⁻¹ := by group
    refine ⟨U₁.mul_mem h1 (U₁.inv_mem huU), ?_⟩
    rw [e]
    exact (conjSub t U₁).mul_mem h2 ((conjSub t U₁).inv_mem h3)
  have hWeq : W = U₁ := S.eq_of_commutators_mem hgen hK hdec huU hnc hZW inf_le_left hKW hcomm
  have hle : U₁ ≤ conjSub t U₁ := by
    intro y hy
    have : y ∈ W := hWeq ▸ hy
    exact this.2
  have hcard : Nat.card (conjSub t U₁) ≤ Nat.card U₁ := by rw [natCard_conjSub_eq]
  have heq : U₁ = conjSub t U₁ := Subgroup.eq_of_le_of_card_ge hle hcard
  exact htnU (mem_normalizer_of_conjSub_eq heq.symm)

theorem Setting146.kMoves_case2 (S : Setting146 G T M) {K U₁ U₂ : Subgroup G} {s u : G}
    (hK : K ∈ cComp (mcOf T)) (hL3 : KbarIsL3Two K) (hdec : IsDecompUK T M K U₁ U₂ s)
    (c22 : Conc14622 T M K) (huK : u ∈ ⁅uOfL22 T M, K⁆) (huZ : u ∉ Zz)
    (hN : T ⊓ Subgroup.normalizer (K : Set G) ≤ tZero T u) :
    (∃ x ∈ K, x * u * x⁻¹ ≠ u) ∧
      ∀ t ∈ T, t ∉ tZero T u → ∃ x ∈ K, x * (u * (t * u * t⁻¹)) * x⁻¹ ≠ u * (t * u * t⁻¹) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  obtain ⟨hSec, hU₁U, hU₂U⟩ := S.sec8_of_decomp hK hL3 hdec
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hdec.mem.2
  have hsZ : s ∈ Subgroup.normalizer (Zz : Set G) := S.normalizer_Z.ge (hTH hdec.mem.1)
  have hKU₂ : K ≤ Subgroup.normalizer (U₂ : Set G) := by
    rw [hdec.conj]
    exact le_normalizer_conjSub hsK hSec.KU
  have hu_sup : u ∈ U₁ ⊔ U₂ := by
    rw [← hdec.sup]
    exact Subgroup.mem_sup_left huK
  have part1 : ∃ x ∈ K, x * u * x⁻¹ ≠ u := by
    by_contra hall
    push Not at hall
    apply huZ
    refine hSec.mem_of_fixed_sup hsK hsZ hdec.conj hdec.Z₂ hKU₂ (fun x hx y hy =>
      S.comm_of_mem_conjClosure (sup_le hU₁U hU₂U hx) (sup_le hU₁U hU₂U hy)) hu_sup
      (fun k hk => ?_)
    have h1 : k * u * k⁻¹ = u := hall k hk
    have h2 : k * u = u * k := by
      calc k * u = k * u * k⁻¹ * k := by group
        _ = u * k := by rw [h1]
    rw [show u * k * u⁻¹ * k⁻¹ = 1 by rw [← h2]; group]
    exact Subgroup.one_mem _
  refine ⟨part1, ?_⟩
  intro t htT htn
  have htnK : t ∉ Subgroup.normalizer (K : Set G) := fun h => htn (hN ⟨htT, h⟩)
  set Kp : Subgroup G := conjSub t⁻¹ K with hKp
  have hKpc : Kp ∈ cComp (mcOf T) := map_conj_mem_cComp hK (hTH (T.inv_mem htT))
  have hKpne : Kp ≠ K := by
    intro h
    apply htnK
    have : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_conjSub_eq h
    simpa using Subgroup.inv_mem _ this
  have hcent : ⁅uOfL22 T M, K⁆ ≤ Subgroup.centralizer (Kp : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (c22.2 Kp hKpc hKpne)
  have hcomm : ∀ x ∈ K, x * (t * u * t⁻¹) = (t * u * t⁻¹) * x := by
    intro x hx
    have hk' : t⁻¹ * x * t ∈ Kp := by
      rw [hKp, mem_conjSub]
      simpa [mul_assoc] using hx
    have h1 := Subgroup.mem_centralizer_iff.mp (hcent huK) _ hk'
    calc x * (t * u * t⁻¹) = t * ((t⁻¹ * x * t) * u) * t⁻¹ := by group
      _ = t * (u * (t⁻¹ * x * t)) * t⁻¹ := by rw [h1]
      _ = (t * u * t⁻¹) * x := by group
  obtain ⟨x, hx, hxu⟩ := part1
  refine ⟨x, hx, fun h => hxu ?_⟩
  have hxc : x * (t * u * t⁻¹) * x⁻¹ = t * u * t⁻¹ := by
    rw [hcomm x hx]; group
  calc x * u * x⁻¹ = (x * (u * (t * u * t⁻¹)) * x⁻¹) * (x * (t * u * t⁻¹) * x⁻¹)⁻¹ := by group
    _ = (u * (t * u * t⁻¹)) * (t * u * t⁻¹)⁻¹ := by rw [h, hxc]
    _ = u := by group

end KM

theorem input14624KMoves_of_gen (hgen : A6CoverGen) : Input14624KMoves := by
  intro G _ _ T M S _hB K U₁ U₂ s u hctx
  obtain ⟨_c19, _c20, _c23, hK, c21, c22, hdec, hch⟩ := hctx
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  rcases hch with ⟨hnc2, huU, hunc, hN⟩ | ⟨hc2, huK, huZ, hN⟩
  · have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
      rcases c21 with ⟨hper, -⟩ | ⟨hc2', -⟩ | ⟨Kp, -, -, hHK, -, -, -, -⟩
      · rw [← hper]
        exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
      · exact absurd hc2' hnc2
      · exact hHK
    exact S.kMoves_normal hgen hK hdec hKn huU hunc hN
  · obtain ⟨t, ht, htn, -⟩ := hc2
    have hL3 : KbarIsL3Two K := by
      rcases c21 with ⟨hper, -⟩ | ⟨-, hL3⟩ | ⟨Kp, -, -, hHK, -, -, -, -⟩
      · have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
          rw [← hper]
          exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
        exact absurd (hKn (hTH ht)) htn
      · exact hL3
      · exact absurd (hHK (hTH ht)) htn
    exact S.kMoves_case2 hK hL3 hdec c22 huK huZ hN

end CFSG.Quasithin
