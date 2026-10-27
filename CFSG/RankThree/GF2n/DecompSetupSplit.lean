module

public import CFSG.RankThree.GF2n.DecompSetupNat

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75 CFSG.Open Matrix
open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open scoped MatrixGroups

theorem exists_units_pow_three_ne_one {F : Type} [Field F] [Finite F] (hF : 4 < Nat.card F) :
    ∃ c : Fˣ, c ^ 3 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨g, fun h => ?_⟩
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

theorem exists_diagElt_mulVec_sub {F : Type} [Field F] {c : Fˣ} (hc : c ^ 3 ≠ 1)
    (v : Fin 2 → F) :
    ∃ w : Fin 2 → F, ((diagElt (c ^ 3) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w - w = v := by
  have h1 : (c : F) ^ 3 - 1 ≠ 0 := by
    intro h
    apply hc
    ext
    simpa [sub_eq_zero] using h
  have h2 : ((c : F) ^ 3)⁻¹ - 1 ≠ 0 := by
    intro h
    apply hc
    have : ((c : F) ^ 3)⁻¹ = 1 := by simpa [sub_eq_zero] using h
    ext
    simpa using this
  refine ⟨![v 0 * ((c : F) ^ 3 - 1)⁻¹, v 1 * (((c : F) ^ 3)⁻¹ - 1)⁻¹], ?_⟩
  rw [coe_diagElt]
  ext i
  fin_cases i
  · have e : v 0 * ((c : F) ^ 3 - 1)⁻¹ * (c : F) ^ 3 - v 0 * ((c : F) ^ 3 - 1)⁻¹ = v 0 := by
      rw [← mul_sub_one, mul_assoc, inv_mul_cancel₀ h1, mul_one]
    simpa [dotProduct, Fin.sum_univ_two] using e
  · have e : v 1 * (((c : F) ^ 3)⁻¹ - 1)⁻¹ * ((c : F) ^ 3)⁻¹ - v 1 * (((c : F) ^ 3)⁻¹ - 1)⁻¹ =
        v 1 := by
      rw [← mul_sub_one, mul_assoc, inv_mul_cancel₀ h2, mul_one]
    simpa [dotProduct, Fin.sum_univ_two] using e

theorem add_upperElt_mulVec {F : Type} [Field F] [CharP F 2] (c : Fˣ) (v : Fin 2 → F) :
    v + ((upperElt F 1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
      ((diagElt c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        (((diagElt c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v +
          ((upperElt F 1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ
            (((diagElt c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hcc : (c : F) * (c : F)⁻¹ = 1 := mul_inv_cancel₀ c.ne_zero
  rw [coe_upperElt, coe_diagElt]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · linear_combination (v 0 - (c : F) ^ 2 * v 0) * h2 - v 1 * hcc
  · linear_combination (v 1 - (c : F)⁻¹ ^ 2 * v 1) * h2

variable {G : Type} [Group G] [Finite G]

namespace DecompSetup

variable {A Ab L Lb M : Subgroup G} (S : DecompSetup A Ab L Lb M)
include S

section Quot

variable [(M.subgroupOf (A ⊔ Ab)).Normal]

local notation "πm" => QuotientGroup.mk' (Subgroup.subgroupOf M (A ⊔ Ab))

variable (P : QuotPair ((A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))))
  ((Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))))
include P

theorem not_isComplement' {f : ℕ} (hf : 3 ≤ f)
    (e : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* PSL(2, GaloisField 2 f)) (hTI : IsTI A)
    (hL : ∀ y ∈ A, y * y = 1 → y ∈ L) (X₁ : Subgroup ↥(A ⊔ Ab)) :
    ¬ Subgroup.IsComplement' (M.subgroupOf (A ⊔ Ab)) X₁ := by
  classical
  intro hX₁
  have := S.isCommutative_M
  obtain ⟨F, hF, hFin, hchar, ψ, hcard, hψs, hψk, hψA, s, -, hsM, hsW⟩ :=
    S.decomp_psl P (by omega) e
  have hXN := S.sup_le_normalizer
  have hker : ∀ x : ↥(A ⊔ Ab), ψ x = 1 → (x : G) ∈ M := fun x hx => by
    have : x ∈ M.subgroupOf (A ⊔ Ab) := by rw [← hψk]; exact hx
    exact Subgroup.mem_subgroupOf.mp this
  have hX₁eq : ∀ x ∈ X₁, ∀ x' ∈ X₁, ψ x = ψ x' → x = x' := by
    intro x hx x' hx' he
    have hm : x * x'⁻¹ ∈ M.subgroupOf (A ⊔ Ab) := by
      rw [← hψk, MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    exact mul_inv_eq_one.mp
      (Subgroup.disjoint_def.mp hX₁.disjoint hm (X₁.mul_mem hx (X₁.inv_mem hx')))
  have hX₁surj : ∀ g : SL(2, F), ∃ x ∈ X₁, ψ x = g := by
    intro g
    obtain ⟨x, rfl⟩ := hψs g
    obtain ⟨⟨m, x₁⟩, hmx, -⟩ := (Subgroup.isComplement'_def.mp hX₁).existsUnique x
    refine ⟨x₁.1, x₁.2, ?_⟩
    have hm1 : ψ m.1 = 1 := by
      have hm : m.1 ∈ ψ.ker := by rw [hψk]; exact m.2
      exact hm
    rw [← hmx, map_mul, hm1, one_mul]
  have hF4 : 4 < Nat.card F := by
    rw [hcard]
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc3⟩ := exists_units_pow_three_ne_one hF4
  obtain ⟨u, huX, hu⟩ := hX₁surj (upperElt F 1)
  obtain ⟨h, hhX, hh⟩ := hX₁surj (diagElt c)
  have hUmem : ∀ t : F, upperElt F t ∈ upperUnipotent F := fun t =>
    (mem_upperUnipotent_iff F).mpr ⟨t, rfl⟩
  have hU : ∀ g ∈ upperUnipotent F, ∃ y : ↥(A ⊔ Ab), (y : G) ∈ A ∧ ψ y = g := by
    intro g hg
    rw [← hψA] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hψU : ∀ y : ↥(A ⊔ Ab), (y : G) ∈ A → ψ y ∈ upperUnipotent F := fun y hy => by
    rw [← hψA]
    exact ⟨y, hy, rfl⟩
  have hhU : ∀ g ∈ upperUnipotent F, diagElt c * g * (diagElt c)⁻¹ ∈ upperUnipotent F := by
    intro g hg
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff F).mp hg
    rw [diagElt_mul_upperElt, mul_inv_cancel_right]
    exact hUmem _
  obtain ⟨y, hyA, hy⟩ := hU _ (hUmem 1)
  obtain ⟨u', hu'⟩ : ∃ u' : ↥(A ⊔ Ab), u' = h * u * h⁻¹ := ⟨_, rfl⟩
  have hu'X : u' ∈ X₁ := by
    rw [hu']
    exact X₁.mul_mem (X₁.mul_mem hhX huX) (X₁.inv_mem hhX)
  have hψu' : ψ u' ∈ upperUnipotent F := by
    rw [hu', map_mul, map_mul, map_inv, hh, hu]
    exact hhU _ (hUmem 1)
  obtain ⟨y', hy'A, hy'⟩ := hU _ hψu'
  have huu : u * u = 1 := hX₁eq _ (X₁.mul_mem huX huX) _ X₁.one_mem (by
    rw [map_mul, hu, upperElt_mul, CharTwo.add_self_eq_zero, upperElt_zero, map_one])
  have huu' : u * u' = u' * u := by
    refine hX₁eq _ (X₁.mul_mem huX hu'X) _ (X₁.mul_mem hu'X huX) ?_
    obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff F).mp hψu'
    rw [map_mul, map_mul, hu, ht, upperElt_mul, upperElt_mul, add_comm]
  have huuG : (u : G) * u = 1 := congrArg Subtype.val huu
  have huu'G : (u : G) * u' = (u' : G) * u := congrArg Subtype.val huu'
  have hu'G : (u' : G) = (h : G) * u * (h : G)⁻¹ := by rw [hu']; rfl
  have hu'u'G : (u' : G) * u' = 1 := by
    rw [hu'G, show (h : G) * u * (h : G)⁻¹ * ((h : G) * u * (h : G)⁻¹) =
      (h : G) * ((u : G) * u) * (h : G)⁻¹ by group, huuG, mul_one, mul_inv_cancel]
  have hNM : ∀ x : ↥(A ⊔ Ab), ∀ m ∈ M, (x : G) * m * (x : G)⁻¹ ∈ M := fun x m hm =>
    (Subgroup.mem_normalizer_iff.mp (hXN x.2) m).mp hm
  have hNM' : ∀ x : ↥(A ⊔ Ab), ∀ m ∈ M, (x : G)⁻¹ * m * x ∈ M := fun x m hm => by
    have := hNM x⁻¹ m hm
    rwa [Subgroup.coe_inv, inv_inv] at this
  have hhA : ∀ z ∈ A, (h : G) * z * (h : G)⁻¹ ∈ A := by
    obtain ⟨a₀, ha₀, ha₀L⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
    set a₀' : ↥(A ⊔ Ab) := ⟨a₀, Subgroup.mem_sup_left ha₀⟩
    obtain ⟨t₀, ht₀⟩ := (mem_upperUnipotent_iff F).mp (hψU a₀' ha₀)
    obtain ⟨a₁, ha₁, ha₁ψ⟩ := hU (ψ (h * a₀' * h⁻¹)) (by
      rw [map_mul, map_mul, map_inv, hh, ht₀]
      exact hhU _ (hUmem _))
    have hm₁ : (a₁ : G)⁻¹ * ((h : G) * a₀ * (h : G)⁻¹) ∈ M :=
      hker (a₁⁻¹ * (h * a₀' * h⁻¹)) (by rw [map_mul, map_inv, ha₁ψ, inv_mul_cancel])
    have hLA : L ≤ conjSubgroup (h : G) A := by
      intro l hl
      rw [mem_conjSubgroup]
      have hlM : (h : G)⁻¹ * l * h ∈ M := hNM' h l (S.L_le_M hl)
      have h1 : ((h : G) * a₀ * (h : G)⁻¹) * l = l * ((h : G) * a₀ * (h : G)⁻¹) := by
        obtain ⟨m₁, hm₁e⟩ : ∃ m₁ : G, m₁ = (a₁ : G)⁻¹ * ((h : G) * a₀ * (h : G)⁻¹) := ⟨_, rfl⟩
        have he : (h : G) * a₀ * (h : G)⁻¹ = a₁ * m₁ := by rw [hm₁e, mul_inv_cancel_left]
        rw [← hm₁e] at hm₁
        have c1 := S.comm_A _ ha₁ _ (S.L_le hl)
        have c2 := S.comm_M _ hm₁ _ (S.L_le_M hl)
        rw [he]
        calc (a₁ : G) * m₁ * l = a₁ * (m₁ * l) := by group
          _ = a₁ * (l * m₁) := by rw [c2]
          _ = (a₁ * l) * m₁ := by group
          _ = (l * a₁) * m₁ := by rw [c1]
          _ = l * (a₁ * m₁) := by group
      have hcomm : a₀ * ((h : G)⁻¹ * l * h) = ((h : G)⁻¹ * l * h) * a₀ := by
        calc a₀ * ((h : G)⁻¹ * l * h) = (h : G)⁻¹ * (((h : G) * a₀ * (h : G)⁻¹) * l) * h := by
              group
          _ = (h : G)⁻¹ * (l * ((h : G) * a₀ * (h : G)⁻¹)) * h := by rw [h1]
          _ = ((h : G)⁻¹ * l * h) * a₀ := by group
      exact S.L_le (S.cent a₀ ha₀ ha₀L _ hlM hcomm)
    have hL1 : L ≠ ⊥ := by
      intro hbot
      have h2 : a₀ * a₀ ∈ L := S.sq_A a₀ ha₀
      rw [hbot, Subgroup.mem_bot] at h2
      exact ha₀L (hL a₀ ha₀ h2)
    have hAeq : conjSubgroup (h : G) A = A := conjSubgroup_eq_of_isTI hTI fun hbot => hL1 (by
      rw [eq_bot_iff]
      intro l hl
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨S.L_le hl, hLA hl⟩)
    intro z hz
    have hz' : (h : G) * z * (h : G)⁻¹ ∈ conjSubgroup (h : G) A := by
      rw [mem_conjSubgroup, show (h : G)⁻¹ * ((h : G) * z * (h : G)⁻¹) * h = z by group]
      exact hz
    rwa [hAeq] at hz'
  obtain ⟨n, hn⟩ : ∃ n : G, n = (y : G) * (u : G)⁻¹ := ⟨_, rfl⟩
  have hnM : n ∈ M := by
    rw [hn]
    exact hker (y * u⁻¹) (by rw [map_mul, map_inv, hy, hu, mul_inv_cancel])
  obtain ⟨n', hn'⟩ : ∃ n' : G, n' = (y' : G) * (u' : G)⁻¹ := ⟨_, rfl⟩
  have hn'M : n' ∈ M := by
    rw [hn']
    exact hker (y' * u'⁻¹) (by rw [map_mul, map_inv, hy', mul_inv_cancel])
  have hyn : (y : G) = n * u := by rw [hn, inv_mul_cancel_right]
  have hyn' : (y' : G) = n' * u' := by rw [hn', inv_mul_cancel_right]
  have hF1 : (y : G) * y = n * ((u : G) * n * (u : G)⁻¹) := by
    rw [hyn]
    calc n * u * (n * u) = n * ((u : G) * n * (u : G)⁻¹) * ((u : G) * u) := by group
      _ = _ := by rw [huuG, mul_one]
  have hF1' : (y' : G) * y' = n' * ((u' : G) * n' * (u' : G)⁻¹) := by
    rw [hyn']
    calc n' * u' * (n' * u') = n' * ((u' : G) * n' * (u' : G)⁻¹) * ((u' : G) * u') := by group
      _ = _ := by rw [hu'u'G, mul_one]
  have hF2 : n * ((u : G) * n' * (u : G)⁻¹) = n' * ((u' : G) * n * (u' : G)⁻¹) := by
    have hyy' : (y : G) * y' = y' * y := S.comm_A _ hyA _ hy'A
    have e1 : (y : G) * y' = n * ((u : G) * n' * (u : G)⁻¹) * ((u : G) * u') := by
      rw [hyn, hyn']
      group
    have e2 : (y' : G) * y = n' * ((u' : G) * n * (u' : G)⁻¹) * ((u' : G) * u) := by
      rw [hyn, hyn']
      group
    rw [e1, e2, huu'G] at hyy'
    exact mul_right_cancel hyy'
  have hF2' : n' * ((u : G) * n' * (u : G)⁻¹) = n * ((u' : G) * n * (u' : G)⁻¹) := by
    have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right (S.sq_M n hnM)
    have ha : (u : G) * n' * (u : G)⁻¹ = n * (n' * ((u' : G) * n * (u' : G)⁻¹)) := by
      calc (u : G) * n' * (u : G)⁻¹ = n⁻¹ * (n * ((u : G) * n' * (u : G)⁻¹)) := by group
        _ = n⁻¹ * (n' * ((u' : G) * n * (u' : G)⁻¹)) := by rw [hF2]
        _ = n * (n' * ((u' : G) * n * (u' : G)⁻¹)) := by rw [hninv]
    rw [ha, ← mul_assoc, ← mul_assoc, S.comm_M n' hn'M n hnM, mul_assoc n n' n',
      S.sq_M n' hn'M, mul_one]
  have hF3 : (h : G) * ((y : G) * y) * (h : G)⁻¹ = (y' : G) * y' := by
    have hzA : (h : G) * y * (h : G)⁻¹ ∈ A := hhA _ hyA
    have hψz : ψ (h * y * h⁻¹) = ψ y' := by
      rw [hy', hu']
      simp only [map_mul, map_inv, hy, hu]
    obtain ⟨l, hl⟩ : ∃ l : G, l = (h : G) * y * (h : G)⁻¹ * (y' : G)⁻¹ := ⟨_, rfl⟩
    have hzl : (h : G) * y * (h : G)⁻¹ = l * y' := by rw [hl, inv_mul_cancel_right]
    have hlM : l ∈ M := by
      rw [hl]
      exact hker (h * y * h⁻¹ * y'⁻¹) (by rw [map_mul, map_inv, hψz, mul_inv_cancel])
    have hlA : l ∈ A := by
      rw [hl]
      exact A.mul_mem hzA (A.inv_mem hy'A)
    have hcomm := S.comm_A l hlA _ hy'A
    calc (h : G) * ((y : G) * y) * (h : G)⁻¹ =
        ((h : G) * y * (h : G)⁻¹) * ((h : G) * y * (h : G)⁻¹) := by group
      _ = l * y' * (l * y') := by rw [hzl]
      _ = l * (y' * l) * y' := by group
      _ = l * (l * y') * y' := by rw [hcomm]
      _ = (l * l) * ((y' : G) * y') := by group
      _ = (y' : G) * y' := by rw [S.sq_M l hlM, one_mul]
  have htop : ∀ K : Subgroup ↥M, (∀ W ∈ s, ∀ w ∈ W, ∀ hwM : w ∈ M, (⟨w, hwM⟩ : ↥M) ∈ K) →
      ∀ m : ↥M, m ∈ K := by
    intro K hK m
    have hle : s.sup id ≤ K.map M.subtype :=
      Finset.sup_le fun W hW w hw => ⟨⟨w, (hsW W hW).1 hw⟩, hK W hW w hw _, rfl⟩
    have hm : (m : G) ∈ s.sup id := by
      rw [hsM]
      exact m.2
    obtain ⟨k, hk, hkm⟩ := hle hm
    rwa [show k = m from Subtype.ext hkm] at hk
  have hθ : ∀ W ∈ s, ∀ w ∈ W, ∃ θ : (Fin 2 → F) → G, (∀ v v', θ (v + v') = θ v * θ v') ∧
      (∀ (x : ↥(A ⊔ Ab)) (v : Fin 2 → F),
        θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = (x : G) * θ v * (x : G)⁻¹) ∧
      (∀ v, θ v ∈ W) ∧ ∃ v, θ v = w := by
    intro W hW w hw
    obtain ⟨θ, hadd, -, hrange, hequiv⟩ := (hsW W hW).2.2.2.2
    refine ⟨θ, hadd, fun x v => (hequiv x v).trans rfl, fun v => ?_, ?_⟩
    · show θ v ∈ (W : Set G)
      rw [← hrange]
      exact ⟨v, rfl⟩
    · have hw' : w ∈ (W : Set G) := hw
      rw [← hrange] at hw'
      exact hw'
  have hNu : (u : G) ∈ Subgroup.normalizer (M : Set G) := hXN u.2
  have hNh : (h : G) ∈ Subgroup.normalizer (M : Set G) := hXN h.2
  set Φ₁ : ↥M →* ↥M := MonoidHom.id ↥M * conjHom M u hNu with hΦ₁
  set Φ₂ : ↥M →* ↥M := (conjHom M h hNh).comp (Φ₁.comp (conjHom M h hNh)) with hΦ₂
  have hN2 : ∀ m : ↥M, Φ₁ m = Φ₂ m := by
    intro m
    refine htop (MonoidHom.eqLocus Φ₁ Φ₂) ?_ m
    intro W hW w hw hwM
    obtain ⟨θ, hadd, hequiv, -, v, rfl⟩ := hθ W hW w hw
    show Φ₁ ⟨θ v, hwM⟩ = Φ₂ ⟨θ v, hwM⟩
    apply Subtype.ext
    show θ v * ((u : G) * θ v * (u : G)⁻¹) = (h : G) * (((h : G) * θ v * (h : G)⁻¹) *
      ((u : G) * ((h : G) * θ v * (h : G)⁻¹) * (u : G)⁻¹)) * (h : G)⁻¹
    simp only [← hequiv, ← hadd]
    rw [hu, hh, add_upperElt_mulVec c v]
  have hN2G : ∀ m ∈ M, m * ((u : G) * m * (u : G)⁻¹) = (h : G) * (((h : G) * m * (h : G)⁻¹) *
      ((u : G) * ((h : G) * m * (h : G)⁻¹) * (u : G)⁻¹)) * (h : G)⁻¹ :=
    fun m hm => congrArg Subtype.val (hN2 ⟨m, hm⟩)
  have hconj' : ∀ m : G, m * ((u' : G) * m * (u' : G)⁻¹) =
      (h : G) * (((h : G)⁻¹ * m * h) * ((u : G) * ((h : G)⁻¹ * m * h) * (u : G)⁻¹)) *
        (h : G)⁻¹ := fun m => by
    rw [hu'G]
    group
  have k1 : n * ((u : G) * n * (u : G)⁻¹) =
      ((h : G)⁻¹ * n' * h) * ((u : G) * ((h : G)⁻¹ * n' * h) * (u : G)⁻¹) := by
    have h3 := hF3
    rw [hF1, hF1', hconj'] at h3
    calc n * ((u : G) * n * (u : G)⁻¹) =
        (h : G)⁻¹ * ((h : G) * (n * ((u : G) * n * (u : G)⁻¹)) * (h : G)⁻¹) * h := by group
      _ = (h : G)⁻¹ * ((h : G) * (((h : G)⁻¹ * n' * h) *
          ((u : G) * ((h : G)⁻¹ * n' * h) * (u : G)⁻¹)) * (h : G)⁻¹) * h := by rw [h3]
      _ = _ := by group
  have k2 : ((h : G)⁻¹ * n' * h) * ((u : G) * ((h : G)⁻¹ * n' * h) * (u : G)⁻¹) =
      (h : G) * (n' * ((u : G) * n' * (u : G)⁻¹)) * (h : G)⁻¹ := by
    rw [hN2G _ (hNM' h n' hn'M), show (h : G) * ((h : G)⁻¹ * n' * h) * (h : G)⁻¹ = n' by group]
  have k3 : n * ((u' : G) * n * (u' : G)⁻¹) =
      (h : G) * ((h : G) * (n * ((u : G) * n * (u : G)⁻¹)) * (h : G)⁻¹) * (h : G)⁻¹ := by
    rw [hconj', hN2G _ (hNM' h n hnM),
      show (h : G) * ((h : G)⁻¹ * n * h) * (h : G)⁻¹ = n by group]
  have hh3G : (h : G) ^ 3 = (h : G) * h * h := by rw [pow_succ, pow_succ, pow_one]
  have hfix : (h : G) ^ 3 * ((y : G) * y) * ((h : G) ^ 3)⁻¹ = (y : G) * y := by
    rw [hF1, hh3G]
    calc (h : G) * h * h * (n * ((u : G) * n * (u : G)⁻¹)) * ((h : G) * h * h)⁻¹ =
        (h : G) * ((h : G) * ((h : G) * (n * ((u : G) * n * (u : G)⁻¹)) * (h : G)⁻¹) *
          (h : G)⁻¹) * (h : G)⁻¹ := by group
      _ = (h : G) * (n * ((u' : G) * n * (u' : G)⁻¹)) * (h : G)⁻¹ := by rw [k3]
      _ = (h : G) * (n' * ((u : G) * n' * (u : G)⁻¹)) * (h : G)⁻¹ := by rw [hF2']
      _ = n * ((u : G) * n * (u : G)⁻¹) := by rw [← k2, ← k1]
  have hNh3 : (h : G) ^ 3 ∈ Subgroup.normalizer (M : Set G) := Subgroup.pow_mem _ hNh 3
  set E : ↥M →* ↥M := conjHom M ((h : G) ^ 3) hNh3 * (MonoidHom.id ↥M)⁻¹ with hE
  have hh3 : ψ (h ^ 3) = diagElt (c ^ 3) := by
    rw [map_pow, hh]
    simp only [pow_succ, pow_zero, one_mul, diagElt_mul_diagElt]
  have hEs : Function.Surjective E := by
    intro m
    obtain ⟨m', hm'⟩ := htop E.range (fun W hW w hw hwM => by
      obtain ⟨θ, hadd, hequiv, hθW, v, rfl⟩ := hθ W hW w hw
      obtain ⟨w', hw'⟩ := exists_diagElt_mulVec_sub hc3 v
      refine ⟨⟨θ w', (hsW W hW).1 (hθW w')⟩, Subtype.ext ?_⟩
      show (h : G) ^ 3 * θ w' * ((h : G) ^ 3)⁻¹ * (θ w')⁻¹ = θ v
      have hθs := hadd (((diagElt (c ^ 3) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w' - w') w'
      rw [sub_add_cancel] at hθs
      rw [show (h : G) ^ 3 = ((h ^ 3 : ↥(A ⊔ Ab)) : G) from (SubmonoidClass.coe_pow h 3).symm,
        ← hequiv, hh3, hθs, mul_inv_cancel_right, hw']) m
    exact ⟨m', hm'⟩
  have hEi : Function.Injective E := Finite.injective_iff_surjective.mpr hEs
  have hyyM : (y : G) * y ∈ M := S.L_le_M (S.sq_A _ hyA)
  have hE1 : E ⟨(y : G) * y, hyyM⟩ = E 1 := by
    rw [map_one]
    apply Subtype.ext
    show (h : G) ^ 3 * ((y : G) * y) * ((h : G) ^ 3)⁻¹ * ((y : G) * y)⁻¹ = 1
    rw [hfix, mul_inv_cancel]
  have hyy : (y : G) * y = 1 := congrArg Subtype.val (hEi hE1)
  have hyM : (y : G) ∈ M := S.L_le_M (hL _ hyA hyy)
  have hψy : ψ y = 1 := by
    have : y ∈ M.subgroupOf (A ⊔ Ab) := Subgroup.mem_subgroupOf.mpr hyM
    rw [← hψk] at this
    exact this
  rw [hy] at hψy
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hψy
  simp [coe_upperElt] at this

end Quot

end DecompSetup

end CFSG.RankThree.GF2n
