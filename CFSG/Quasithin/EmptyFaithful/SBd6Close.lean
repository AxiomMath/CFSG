module

public import CFSG.Quasithin.EmptyFaithful.SBd5UL
public import CFSG.Quasithin.EmptyFaithful.SBd6Tw
public import CFSG.Quasithin.EmptyFaithful.SBd2L3Branch2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace SBd6

section Module

variable {G : Type} [Group G]

omit [Group G] in
theorem det_eq_one_of_mem_statedSL {n : ℕ} {F : Type} [Field F]
    (g : CFSG.Assembly.LowTwoRank.StatedSL n F) :
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  obtain ⟨x, hx⟩ := g
  rw [CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL] at hx
  obtain ⟨A, hA⟩ := hx
  show (x : Matrix (Fin n) (Fin n) F).det = 1
  rw [← hA]
  exact A.2

theorem comm_mem_pCore_of_module [Finite G] {L Z C : Subgroup G} {k n : ℕ} (hk0 : 0 < k) {F : Type}
    [Field F] [Fintype F] (hFc : Fintype.card F = 2 ^ n)
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj L α)
    (hq : IsLnTwoQuot L 3) (hZ : IsSumOfNaturalModulesVia L Z C α false k) {r y : G}
    (hrZ : r ∈ Subgroup.normalizer (Z : Set G)) (hrL : r ∈ Subgroup.normalizer (L : Set G))
    (hrC : r ∈ Subgroup.normalizer (C : Set G)) (hy : y ∈ L) (hyr : r * y = y * r)
    (hy3 : orderOf y = 3) (hr2 : ∃ m : ℕ, r ^ (2 ^ m) = 1) :
    ∀ l ∈ L, r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  obtain ⟨hLZ, -, β, hβs, hβk, hβe⟩ := hZ
  let act : ↥L → Matrix (Fin 3) (Fin 3) F := fun a =>
    ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have hdet : ∀ l, (act l).det = 1 := fun l => det_eq_one_of_mem_statedSL (α l)
  have hker : ∀ (u : ↥Z) (hu : r * u * r⁻¹ ∈ Z), β ⟨r * u * r⁻¹, hu⟩ = 1 ↔ β u = 1 := by
    intro u hu
    have h1 : ∀ v : ↥Z, β v = 1 ↔ (v : G) ∈ C := by
      intro v
      rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
    rw [h1, h1]
    exact (Subgroup.mem_normalizer_iff.mp hrC (u : G)).symm
  have hy3' : (⟨y, hy⟩ : ↥L) ^ 3 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one y
    rw [hy3] at this
    simpa using this
  have hσ3 : (act ⟨y, hy⟩) ^ 3 = 1 := by
    have h1 : α ⟨y, hy⟩ ^ 3 = 1 := by rw [← map_pow, hy3', map_one]
    have h2 : (((α ⟨y, hy⟩ ^ 3 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 := by rw [h1]; rfl
    simpa [act] using h2
  have hσ1 : act ⟨y, hy⟩ ≠ 1 := by
    intro h
    have hα1 : α ⟨y, hy⟩ = 1 := by
      apply Subtype.ext
      apply Units.ext
      simpa [act] using h
    have hmem : (⟨y, hy⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hα.2]
      exact hα1
    have hpc : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := by
      exact CFSG.LieType.BorelTits.pCore_isPGroup 2
    obtain ⟨j, hj⟩ := hpc ⟨⟨y, hy⟩, hmem⟩
    have hyj : y ^ (2 ^ j) = 1 := by
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hj
      simpa using this
    have hd : 3 ∣ 2 ^ j := by
      rw [← hy3]
      exact orderOf_dvd_of_pow_eq_one hyj
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)
    omega
  obtain ⟨m, hm⟩ := hr2
  have key := twist_trivial hF hk0 act hdet (SBd5.act_surj hα.1) β hβs hLZ
    (fun a u v huv i => by simpa [moduleAct] using hβe a u v huv i) hrZ hrL hker hy hyr hσ3 hσ1 hm
  intro l hl
  have hrl : r * l * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hrL l).mp hl
  have h1 := key ⟨l, hl⟩ hrl
  have hα2 : α ⟨r * l * r⁻¹, hrl⟩ = α ⟨l, hl⟩ := by
    apply Subtype.ext
    apply Units.ext
    exact h1
  have hmem : (⟨r * l * r⁻¹ * l⁻¹, L.mul_mem hrl (L.inv_mem hl)⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hα.2, MonoidHom.mem_ker]
    have : (⟨r * l * r⁻¹ * l⁻¹, L.mul_mem hrl (L.inv_mem hl)⟩ : ↥L) =
        ⟨r * l * r⁻¹, hrl⟩ * (⟨l, hl⟩ : ↥L)⁻¹ := rfl
    rw [this, map_mul, map_inv, hα2, mul_inv_cancel]
  exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

theorem case5_comm [Finite G] {L Q C U : Subgroup G}
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα : IsModO2Surj L α)
    (hZ : IsSumOfNaturalModulesVia L Q C α false 1) (hC2 : Nat.card C = 2)
    (hCL : C ≤ Subgroup.centralizer (L : Set G)) (hUQ : U ≤ Q)
    (hUc : ∀ u ∈ U, ∀ q ∈ Q, u * q = q * u) (hUL : L ≤ Subgroup.normalizer (U : Set G))
    (hUU : ⁅U, L⁆ = U) (hU0 : U ≠ ⊥) : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  obtain ⟨hLQ, -, β, hβs, hβk, hβe⟩ := hZ
  have hkerQ : ∀ v : ↥Q, β v = 1 ↔ (v : G) ∈ C := by
    intro v
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  obtain ⟨u₀, hu₀, hu₀C⟩ : ∃ u₀ ∈ U, u₀ ∉ C := by
    by_contra h
    push Not at h
    apply hU0
    have hUC : U ≤ Subgroup.centralizer (L : Set G) := fun u hu => hCL (h u hu)
    rw [← hUU]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUC
  let X : AddSubgroup (Fin 3 → ZMod 2) :=
    { carrier := {x | ∃ u : ↥Q, (u : G) ∈ U ∧ Multiplicative.toAdd (β u) 0 = x}
      zero_mem' := ⟨1, U.one_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, rfl⟩
        refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, ?_⟩
        simp
      neg_mem' := by
        rintro _ ⟨u₁, hu₁, rfl⟩
        refine ⟨u₁⁻¹, U.inv_mem hu₁, ?_⟩
        show Multiplicative.toAdd (β u₁⁻¹) 0 = -(Multiplicative.toAdd (β u₁) 0)
        rw [map_inv, toAdd_inv]
        rfl }
  have hXinv : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∀ x ∈ X,
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x ∈ X := by
    intro g x hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨l, hl⟩ := SBd5.act_surj hα.1 g
    have hlu : (l : G) * (u : G) * (l : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp u.2
    have hluU : (l : G) * (u : G) * (l : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hUL l.2) _).mp hu
    refine ⟨⟨_, hlu⟩, hluU, ?_⟩
    have := hβe l u ⟨_, hlu⟩ rfl 0
    rw [this]
    have h' : moduleAct false (α l : GL (Fin 3) (ZMod 2)) =
        ((α l : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by simp [moduleAct]
    rw [h', ← hl]
  have hXtop : X = ⊤ := by
    rcases SBd6.irreducible_vec (F := ZMod 2) (by simp) X hXinv with h | h
    · exfalso
      have hβu₀ : β ⟨u₀, hUQ hu₀⟩ ≠ 1 := fun h' => hu₀C ((hkerQ _).mp h')
      apply hβu₀
      have hmem : Multiplicative.toAdd (β ⟨u₀, hUQ hu₀⟩) 0 ∈ X := ⟨⟨u₀, hUQ hu₀⟩, hu₀, rfl⟩
      rw [h] at hmem
      have h0 : Multiplicative.toAdd (β ⟨u₀, hUQ hu₀⟩) 0 = 0 := by simpa using hmem
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa using h0
    · exact h
  have hdec : ∀ q ∈ Q, ∃ u ∈ U, ∃ c ∈ C, q = u * c := by
    intro q hq
    have hmem : Multiplicative.toAdd (β ⟨q, hq⟩) 0 ∈ X := by rw [hXtop]; exact AddSubgroup.mem_top _
    obtain ⟨u, huU, hu⟩ := hmem
    refine ⟨u, huU, (u : G)⁻¹ * q, ?_, by group⟩
    have h1 : β u = β ⟨q, hq⟩ := by
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact hu
    have : β (u⁻¹ * ⟨q, hq⟩) = 1 := by
      rw [map_mul, map_inv, h1]
      exact inv_mul_cancel _
    exact (hkerQ _).mp this
  have hCcomm : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ * c₂ = c₂ * c₁ := by
    intro c₁ hc₁ c₂ hc₂
    have := Fintype.ofFinite G
    by_cases h1 : c₁ = 1
    · rw [h1]; simp
    by_cases h2 : c₂ = 1
    · rw [h2]; simp
    have h3 := SBd5.eq_of_card_two hC2 (a := ⟨c₁, hc₁⟩) (b := ⟨c₂, hc₂⟩)
      (fun h => h1 (congrArg Subtype.val h)) (fun h => h2 (congrArg Subtype.val h))
    have h4 : c₁ = c₂ := congrArg Subtype.val h3
    rw [h4]
  intro a ha b hb
  obtain ⟨u₁, hu₁, c₁, hc₁, rfl⟩ := hdec a ha
  obtain ⟨u₂, hu₂, c₂, hc₂, rfl⟩ := hdec b hb
  have hc₁Q : c₁ ∈ Q := by
    have : (u₁ : G)⁻¹ * (u₁ * c₁) ∈ Q := Q.mul_mem (Q.inv_mem (hUQ hu₁)) ha
    simpa using this
  have hc₂Q : c₂ ∈ Q := by
    have : (u₂ : G)⁻¹ * (u₂ * c₂) ∈ Q := Q.mul_mem (Q.inv_mem (hUQ hu₂)) hb
    simpa using this
  calc u₁ * c₁ * (u₂ * c₂) = u₁ * (c₁ * u₂) * c₂ := by group
    _ = u₁ * (u₂ * c₁) * c₂ := by rw [hUc u₂ hu₂ c₁ hc₁Q |>.symm]
    _ = (u₁ * u₂) * (c₁ * c₂) := by group
    _ = (u₂ * u₁) * (c₂ * c₁) := by
      rw [hUc u₁ hu₁ u₂ (hUQ hu₂), hCcomm c₁ hc₁ c₂ hc₂]
    _ = u₂ * (u₁ * c₂) * c₁ := by group
    _ = u₂ * (c₂ * u₁) * c₁ := by rw [hUc u₁ hu₁ c₂ hc₂Q]
    _ = u₂ * c₂ * (u₁ * c₁) := by group

omit [Group G] in
theorem comm_le_of_decomp {G : Type} [Group G] {V Vc Vn YL : Subgroup G}
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsup : Vc ⊔ Vn = V)
    (hYLc : YL ≤ Subgroup.centralizer (Vc : Set G)) (hYLn : YL ≤ Subgroup.normalizer (Vn : Set G)) :
    ⁅V, YL⁆ ≤ Vn := by
  refine Subgroup.commutator_le.mpr fun v hv y hy => ?_
  have hVcV : Vc ≤ V := hsup ▸ le_sup_left
  have hVnV : Vn ≤ V := hsup ▸ le_sup_right
  obtain ⟨a, ha, b, hb, rfl⟩ := SBd2.exists_mul_of_mem_sup'
    (fun a ha b hb => hVab a (hVcV ha) b (hVnV hb)) (hsup ▸ hv)
  have hya : y * a = a * y := (Subgroup.mem_centralizer_iff.mp (hYLc hy) a ha).symm
  have h1 : y * b * y⁻¹ ∈ Vn := (Subgroup.mem_normalizer_iff.mp (hYLn hy) b).mp hb
  have h2 : b * (y * b⁻¹ * y⁻¹) ∈ Vn := Vn.mul_mem hb (by
    have := (Subgroup.mem_normalizer_iff.mp (hYLn hy) b⁻¹).mp (Vn.inv_mem hb)
    exact this)
  have e : ⁅a * b, y⁆ = a * (b * (y * b⁻¹ * y⁻¹)) * a⁻¹ := by
    have hya' : y * a⁻¹ * y⁻¹ = a⁻¹ := by
      have : y * a⁻¹ = a⁻¹ * y := by
        calc y * a⁻¹ = a⁻¹ * (a * y) * a⁻¹ := by group
          _ = a⁻¹ * (y * a) * a⁻¹ := by rw [hya]
          _ = a⁻¹ * y := by group
      rw [this]; group
    simp only [commutatorElement_def]
    calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * b * y * b⁻¹ * a⁻¹ * y⁻¹ := by group
      _ = a * b * y * b⁻¹ * (y⁻¹ * (y * a⁻¹ * y⁻¹)) := by group
      _ = a * b * y * b⁻¹ * (y⁻¹ * a⁻¹) := by rw [hya']
      _ = a * (b * (y * b⁻¹ * y⁻¹)) * a⁻¹ := by
        have : a * b * y * b⁻¹ * (y⁻¹ * a⁻¹) = a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ := by group
        rw [this]; group
  rw [e]
  have hcomm : a * (b * (y * b⁻¹ * y⁻¹)) * a⁻¹ = b * (y * b⁻¹ * y⁻¹) := by
    have := hVab a (hVcV ha) _ (hVnV h2)
    rw [this]; group
  rw [hcomm]
  exact h2

end Module

end SBd6

end CFSG.Quasithin
