module

public import CFSG.Milestones.ASVolI.C135.Cent
public import CFSG.Milestones.ASVolI.C135.P1
public import CFSG.Milestones.ASVolI.C135.Syl

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (crd crd_injective crd_conj_false le_normalizer_centerOf slNat
  slNat_surjective)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Part5

variable {X R L S : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)}

theorem burnsideC135_card_fix_U_le (hS : IsSylowTwoOf S X) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hα : IsModO2Surj L α) {Q : Subgroup G}
    (h1 : IsSumOfNaturalModulesVia L (centerOf Q) ⊥ α false 1) :
    Nat.card ↥(centerOf Q ⊓ Subgroup.centralizer (S : Set G)) ≤ Fintype.card F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρ := slNat_surjective hα.1
  obtain ⟨hPg, hodd⟩ := burnsideC135_image_sylow hS hLX hXL hρ
  set T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) F) := hPg.toSylow hodd with hT
  obtain ⟨y₀, -, hnat, -⟩ := burnsideC135_sylow_fix T
  have hfix : ∀ u : ↥(centerOf Q ⊓ Subgroup.centralizer (S : Set G)),
      ∃ c : F, crd h1 ⟨u, u.2.1⟩ 0 = c • y₀ := by
    intro u
    refine hnat _ fun t ht => ?_
    have ht' : t ∈ ((S ⊓ L).subgroupOf L).map (slNat α) := (IsPGroup.mem_toSylow hPg hodd).mp ht
    obtain ⟨l, hl0, rfl⟩ := ht'
    have hl : (l : G) ∈ S ⊓ L := hl0
    have hlu : (l : G) * u * (l : G)⁻¹ = u := by
      have h2 := Subgroup.mem_centralizer_iff.mp u.2.2 _ hl.1
      calc (l : G) * u * (l : G)⁻¹ = u * l * (l : G)⁻¹ := by rw [h2]
        _ = u := by group
    have h3 := crd_conj_false h1 l ⟨u, u.2.1⟩ ⟨u, u.2.1⟩ hlu.symm
    have h4 := congrFun h3 0
    exact h4.symm
  choose c hc using hfix
  refine (Nat.card_le_card_of_injective c fun u v huv => ?_).trans (Nat.card_eq_fintype_card).le
  have h5 : crd h1 ⟨u, u.2.1⟩ = crd h1 ⟨v, v.2.1⟩ := by
    funext i
    rw [Subsingleton.elim i 0, hc, hc, huv]
  have h6 := crd_injective h1 h5
  exact Subtype.ext (congrArg (fun x : ↥(centerOf Q) => (x : G)) h6)

theorem burnsideC135_card_comm_image {Q W₁ W₂ : Subgroup G}
    {α' : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}
    {βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F)}
    {β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)} {β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)}
    (hD : burnsideC135_DSG Q L W₁ W₂ α' βU β₁ β₂)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf Q)
    (w : ↥W₁) (hw : (w : G) ∉ centerOf Q) (Z₀ : Subgroup G)
    (hZ : ∀ y ∈ W₂, y * w * y⁻¹ * (w : G)⁻¹ ∈ Z₀) :
    Fintype.card F ^ 2 ≤ Nat.card Z₀ := by
  classical
  have hU : ∀ y ∈ W₂, y * w * y⁻¹ * (w : G)⁻¹ ∈ centerOf (Q) := fun y hy =>
    hcomm y (hD.le_Q₂ hy) w (hD.le_Q₁ w.2)
  let f : ↥W₂ →* G :=
    { toFun := fun y => (y : G) * w * (y : G)⁻¹ * (w : G)⁻¹
      map_one' := by simp
      map_mul' := fun y y' => by
        have hc : ((y' : G) * w * (y' : G)⁻¹ * (w : G)⁻¹) * y = y *
            ((y' : G) * w * (y' : G)⁻¹ * (w : G)⁻¹) :=
          burnsideC135_U_comm (hU y' y'.2) (hD.le_Q₂ y.2)
        have hc' : ((y' : G) * w * (y' : G)⁻¹ * (w : G)⁻¹) *
            ((y : G) * w * (y : G)⁻¹ * (w : G)⁻¹) =
            ((y : G) * w * (y : G)⁻¹ * (w : G)⁻¹) *
              ((y' : G) * w * (y' : G)⁻¹ * (w : G)⁻¹) :=
          burnsideC135_U_comm (hU y' y'.2) (hcomm _ (hD.le_Q₂ y.2) _ (hD.le_Q₁ w.2) |>.1)
        show ((y * y' : ↥W₂) : G) * w * ((y * y' : ↥W₂) : G)⁻¹ * (w : G)⁻¹ = _
        simp only [Subgroup.coe_mul, mul_inv_rev]
        calc (y : G) * y' * w * ((y' : G)⁻¹ * (y : G)⁻¹) * (w : G)⁻¹ =
              (y : G) * ((y' : G) * w * (y' : G)⁻¹ * (w : G)⁻¹) * w * (y : G)⁻¹ * (w : G)⁻¹ := by
              group
          _ = ((y' : G) * w * (y' : G)⁻¹ * (w : G)⁻¹) * y * w * (y : G)⁻¹ * (w : G)⁻¹ := by
              rw [← hc]
          _ = ((y' : G) * w * (y' : G)⁻¹ * (w : G)⁻¹) *
                ((y : G) * w * (y : G)⁻¹ * (w : G)⁻¹) := by group
          _ = _ := hc' }
  have hker : Nat.card f.ker = Nat.card ↥(W₂ ⊓ Subgroup.centralizer ({(w : G)} : Set G)) := by
    have e : f.ker = (W₂ ⊓ Subgroup.centralizer ({(w : G)} : Set G)).subgroupOf W₂ := by
      refine Subgroup.ext fun y => ?_
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show (y : G) * w * (y : G)⁻¹ * (w : G)⁻¹ = 1 ↔ (y : G) ∈ W₂ ⊓ Subgroup.centralizer _
      constructor
      · intro h
        refine ⟨y.2, ?_⟩
        show (y : G) ∈ Subgroup.centralizer ({(w : G)} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (y : G) * w = ((y : G) * w * (y : G)⁻¹ * (w : G)⁻¹) * (w * y) := by group
          _ = w * y := by rw [h, one_mul]
      · rintro ⟨-, h⟩
        have h' : (y : G) ∈ Subgroup.centralizer ({(w : G)} : Set G) := h
        rw [Subgroup.mem_centralizer_singleton_iff] at h'
        rw [h']
        group
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [hker, burnsideC135_card_centralizer hD hcomm w hw, burnsideC135_card_U hD,
    burnsideC135_card_dual hD hD.le₂ hD.dual₂_onto hD.dual₂_ker] at h1
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have h2 : Nat.card f.range = Fintype.card F ^ 2 := by
    have h3 : Fintype.card F ^ 3 * Fintype.card F * Nat.card f.range =
        Fintype.card F ^ 3 * Fintype.card F * Fintype.card F ^ 2 := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h3
  rw [← h2]
  refine Subgroup.card_le_of_le ?_
  rintro _ ⟨y, rfl⟩
  exact hZ y y.2

theorem burnsideC135_part5 (hMS : IsMSPair X R) (hL : L ∈ cComp X)
    (hG : (X : Set G) = (L : Set G) * (R : Set G)) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowTwoOf S X) (hα : IsModO2Surj L α) (hQO : pCoreOf 2 L = c134Q X L)
    (hP : pCoreOf 2 X = pCoreOf 2 L)
    (h1 : IsSumOfNaturalModulesVia L (centerOf (c134Q X L)) ⊥ α false 1)
    (h2 : IsSumOfNaturalModulesVia L (c134Q X L) (centerOf (c134Q X L)) α true 2) :
    (Subgroup.upperCentralSeries ↥S 2).map S.subtype ≤ centerOf (pCoreOf 2 L) := by
  classical
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hCU := burnsideC135_centralizer_U_le' hMS hG hα hLX hXL h1
  rw [← hQO] at h1 h2 hCU
  rw [hP] at hCU
  obtain ⟨W₁, W₂, βU, β₁, β₂, hD⟩ := burnsideC135_dualSplit_of_case3 hα h1 h2
  have hcomm : ∀ x ∈ pCoreOf 2 L, ∀ y ∈ pCoreOf 2 L,
      x * y * x⁻¹ * y⁻¹ ∈ centerOf (pCoreOf 2 L) := fun x hx y hy =>
    burnsideC135_comm_mem_U h2 hx hy
  have hQS : pCoreOf 2 L ≤ S := by
    rw [← hP]
    exact CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf hS
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hXL.trans (normalizer_le_normalizer_pCoreOf 2 L)
  have hXU : X ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L) : Set G) :=
    le_normalizer_centerOf hXQ
  have hZS : ∀ c ∈ S, (∀ s ∈ S, c * s = s * c) → c ∈ centerOf (pCoreOf 2 L) := by
    intro c hc hcS
    have hcC : c ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq => (hcS q (hQS hq)).symm
    have hcQ : c ∈ pCoreOf 2 L := hCU ⟨hS.1 hc, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp hcC u hu.1⟩
    exact ⟨hcQ, hcC⟩
  have hfixle := burnsideC135_card_fix_U_le hS hLX hXL hα h1
  rintro _ ⟨z, hz, rfl⟩
  have hz1 : ∀ s : ↥S, ⁅z, s⁆ ∈ Subgroup.center ↥S := by
    intro s
    have h3 := (Subgroup.mem_upperCentralSeries_succ_iff (G := ↥S) (n := 1)).mp hz s
    rwa [Subgroup.upperCentralSeries_one] at h3
  have hzc : ∀ s ∈ S, (z : G) * s * (z : G)⁻¹ * s⁻¹ ∈ centerOf (pCoreOf 2 L) ∧
      ∀ s' ∈ S, ((z : G) * s * (z : G)⁻¹ * s⁻¹) * s' = s' * ((z : G) * s * (z : G)⁻¹ * s⁻¹) := by
    intro s hs
    have h3 := hz1 ⟨s, hs⟩
    rw [Subgroup.mem_center_iff] at h3
    have hcS : ∀ s' ∈ S, ((z : G) * s * (z : G)⁻¹ * s⁻¹) * s' =
        s' * ((z : G) * s * (z : G)⁻¹ * s⁻¹) := by
      intro s' hs'
      have h4 := congrArg Subtype.val (h3 ⟨s', hs'⟩)
      simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at h4
      exact h4.symm
    exact ⟨hZS _ (S.mul_mem (S.mul_mem (S.mul_mem z.2 hs) (S.inv_mem z.2)) (S.inv_mem hs)) hcS,
      hcS⟩
  have hzX : (z : G) ∈ X := hS.1 z.2
  have hzL := burnsideC135_comm_L_of_triv hα h2 (hXL hzX) (hXQ hzX)
    fun q hq => (hzc q (hQS hq)).1
  obtain ⟨m, hm⟩ := hS.2.1 z
  have hzm : (z : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hzU : ∀ u ∈ centerOf (pCoreOf 2 L), (z : G) * u = u * z := fun u hu =>
    burnsideC135_commute_U hα hLQ h1 (hXU hzX) hzL hzm hu
  have hzQ : (z : G) ∈ pCoreOf 2 L :=
    hCU ⟨hzX, Subgroup.mem_centralizer_iff.mpr fun u hu => (hzU u hu).symm⟩
  show (z : G) ∈ centerOf (pCoreOf 2 L)
  by_contra hzU'
  have hQN₂ : pCoreOf 2 L ≤ Subgroup.normalizer (W₂ : Set G) :=
    burnsideC135_le_normalizer_W₁ (burnsideC135_dualSplit_symm hD) hcomm
  have hzW : (z : G) ∈ ((W₁ ⊔ W₂ : Subgroup G) : Set G) := by
    rw [hD.join]
    exact hzQ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right W₁ W₂
    (fun a ha => hQN₂ (hD.le_Q₁ ha))] at hzW
  obtain ⟨w₁, hw₁, w₂, hw₂, hzw⟩ := hzW
  obtain ⟨hsq₁, hsq₂⟩ := burnsideC135_W_sq hD
  set Z₀ := centerOf (pCoreOf 2 L) ⊓ Subgroup.centralizer (S : Set G) with hZ₀
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hcontra : Fintype.card F ^ 2 ≤ Nat.card Z₀ → False := by
    intro h
    have h3 := h.trans hfixle
    nlinarith
  have hyz : ∀ y ∈ pCoreOf 2 L, y * z * y⁻¹ * (z : G)⁻¹ ∈ Z₀ := by
    intro y hy
    obtain ⟨hU', hS'⟩ := hzc y (hQS hy)
    have e : y * z * y⁻¹ * (z : G)⁻¹ = ((z : G) * y * (z : G)⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    refine Z₀.inv_mem ⟨hU', Subgroup.mem_centralizer_iff.mpr fun s hs => (hS' s hs).symm⟩
  by_cases hw₁U : w₁ ∈ centerOf (pCoreOf 2 L)
  ·
    have hw₂U : w₂ ∉ centerOf (pCoreOf 2 L) := by
      intro h
      apply hzU'
      rw [← hzw]
      exact (centerOf (pCoreOf 2 L)).mul_mem hw₁U h
    refine hcontra (burnsideC135_card_comm_image (burnsideC135_dualSplit_symm hD) hcomm
      ⟨w₂, hw₂⟩ hw₂U Z₀ fun y hy => ?_)
    have e : y * w₂ * y⁻¹ * w₂⁻¹ = y * z * y⁻¹ * (z : G)⁻¹ := by
      rw [← hzw]
      have hyw₁ : y * w₁ = w₁ * y := burnsideC135_comm_of_sq hsq₁ hy hw₁
      have hc : (y * w₂ * y⁻¹ * w₂⁻¹) * w₁ = w₁ * (y * w₂ * y⁻¹ * w₂⁻¹) :=
        burnsideC135_U_comm (hcomm y (hD.le_Q₁ hy) w₂ (hD.le_Q₂ hw₂)) (hD.le_Q₁ hw₁)
      calc y * w₂ * y⁻¹ * w₂⁻¹ = w₁ * (y * w₂ * y⁻¹ * w₂⁻¹) * w₁⁻¹ := by
            rw [← hc]; group
        _ = (w₁ * y) * w₂ * y⁻¹ * w₂⁻¹ * w₁⁻¹ := by group
        _ = (y * w₁) * w₂ * y⁻¹ * w₂⁻¹ * w₁⁻¹ := by rw [hyw₁]
        _ = y * (w₁ * w₂) * y⁻¹ * (w₁ * w₂)⁻¹ := by group
    rw [e]
    exact hyz y (hD.le_Q₁ hy)
  ·
    refine hcontra (burnsideC135_card_comm_image hD hcomm ⟨w₁, hw₁⟩ hw₁U Z₀ fun y hy => ?_)
    have e : y * w₁ * y⁻¹ * w₁⁻¹ = y * z * y⁻¹ * (z : G)⁻¹ := by
      rw [← hzw]
      have hyw₂ : y * w₂ = w₂ * y := burnsideC135_comm_of_sq hsq₂ hy hw₂
      calc y * w₁ * y⁻¹ * w₁⁻¹ = y * w₁ * (w₂ * y⁻¹ * w₂⁻¹) * w₁⁻¹ := by
            rw [show w₂ * y⁻¹ * w₂⁻¹ = y⁻¹ by
              rw [show w₂ * y⁻¹ = y⁻¹ * w₂ by
                rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hyw₂, mul_assoc, mul_inv_cancel,
                  mul_one]]
              group]
        _ = y * (w₁ * w₂) * y⁻¹ * (w₁ * w₂)⁻¹ := by group
    rw [e]
    exact hyz y (hD.le_Q₂ hy)

end Part5

end CFSG.ASVolI

end
