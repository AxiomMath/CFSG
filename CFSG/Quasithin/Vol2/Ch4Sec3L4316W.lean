module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316U35
public import CFSG.Quasithin.Vol2.Ch11SecB414A

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups Pointwise commutatorElement

namespace L4316

variable {G : Type} [Group G]

theorem conj_eq_of_perfect [Finite G] {K A B : Subgroup G} (hKp : ⁅K, K⁆ = K)
    (hB : IsPGroup 2 ↥B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B)
    (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ = b)
    (hKA : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ * a⁻¹ ∈ B) {k a : G} (hk : k ∈ K) (ha : a ∈ A) :
    k * a * k⁻¹ = a := by
  have hmem : ∀ k ∈ K, a⁻¹ * (k * a * k⁻¹) ∈ B := by
    intro k hk
    have h1 := hAB a⁻¹ (A.inv_mem ha) _ (hKA k hk a ha)
    have e : a⁻¹ * (k * a * k⁻¹ * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * (k * a * k⁻¹) := by group
    rwa [e] at h1
  let ψ : ↥K →* G :=
    { toFun := fun k => a⁻¹ * ((k : G) * a * (k : G)⁻¹)
      map_one' := by simp
      map_mul' := fun k k' => by
        have hb := hKB k k.2 _ (hmem k' k'.2)
        simp only [Subgroup.coe_mul]
        calc a⁻¹ * ((k : G) * k' * a * ((k : G) * k')⁻¹)
            = a⁻¹ * ((k : G) * a * (k : G)⁻¹) *
                ((k : G) * (a⁻¹ * ((k' : G) * a * (k' : G)⁻¹)) * (k : G)⁻¹) := by group
          _ = _ := by rw [hb] }
  have hrange : ψ.range ≤ B := by
    rintro _ ⟨k, rfl⟩
    exact hmem k k.2
  have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    have htop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hKp]
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥ψ.range := hB.to_le hrange
  have : Group.IsNilpotent ↥ψ.range := hp.isNilpotent
  have hbot := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hperf
  have h1 : ψ ⟨k, hk⟩ = 1 := by
    have h2 : ψ ⟨k, hk⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hbot] at h2
    exact h2
  have h2 : a⁻¹ * (k * a * k⁻¹) = 1 := h1
  calc k * a * k⁻¹ = a * (a⁻¹ * (k * a * k⁻¹)) := by group
    _ = a := by rw [h2, mul_one]

theorem le_normalizer_of_conj [Finite G] {Γ J : Subgroup G}
    (h : ∀ g ∈ Γ, ∀ a ∈ J, g * a * g⁻¹ ∈ J) : Γ ≤ Subgroup.normalizer (J : Set G) :=
  fun g hg => CFSG.Quasithin.A4.mem_normalizer_of_conj_mem (h g hg)

theorem exists_chief [Finite G] {Γ K N : Subgroup G} (hN : IsPGroup 2 ↥N) (hNΓ : N ≤ Γ)
    (hΓN : Γ ≤ Subgroup.normalizer (N : Set G)) (hKp : ⁅K, K⁆ = K)
    (hK : ∃ k ∈ K, ∃ n ∈ N, k * n * k⁻¹ ≠ n) :
    ∃ A B : Subgroup G, A ≤ N ∧ B < A ∧ Γ ≤ Subgroup.normalizer (A : Set G) ∧
      Γ ≤ Subgroup.normalizer (B : Set G) ∧ (∀ a ∈ A, a ^ 2 ∈ B) ∧
      (∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) ∧
      (∀ J : Subgroup G, B ≤ J → J ≤ A → Γ ≤ Subgroup.normalizer (J : Set G) →
        J = B ∨ J = A) ∧
      ∃ k ∈ K, ∃ a ∈ A, k * a * k⁻¹ * a⁻¹ ∉ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let PA : Subgroup G → Prop := fun A => A ≤ N ∧ Γ ≤ Subgroup.normalizer (A : Set G) ∧
    ∃ k ∈ K, ∃ a ∈ A, k * a * k⁻¹ ≠ a
  have hexA : ∃ n, ∃ A, PA A ∧ Nat.card A = n := ⟨_, N, ⟨le_rfl, hΓN, hK⟩, rfl⟩
  obtain ⟨A, hPA, hcardA⟩ := Nat.find_spec hexA
  have hminA : ∀ A', PA A' → Nat.card A ≤ Nat.card A' := fun A' h =>
    hcardA ▸ Nat.find_min' hexA ⟨A', h, rfl⟩
  obtain ⟨hAN, hΓA, k₀, hk₀, a₀, ha₀, hka₀⟩ := hPA
  have hA2 : IsPGroup 2 ↥A := hN.to_le hAN
  have : Fact (IsPGroup 2 ↥A) := ⟨hA2⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Subgroup G, Φ = (frattini ↥A).map A.subtype := ⟨_, rfl⟩
  have hΦA : Φ ≤ A := by
    rw [hΦ]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hΓΦ : Γ ≤ Subgroup.normalizer (Φ : Set G) :=
    hΦ ▸ hΓA.trans (normalizer_le_normalizer_map_of_characteristic (frattini ↥A))
  have hΦlt : Φ < A := by
    refine lt_of_le_of_ne hΦA fun h => ?_
    have hnt : Nontrivial ↥A := by
      refine ⟨⟨⟨a₀, ha₀⟩, 1, fun h1 => hka₀ ?_⟩⟩
      have h2 : a₀ = 1 := congrArg Subtype.val h1
      rw [h2]
      group
    have htop : frattini ↥A = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : G) ∈ Φ := h ▸ x.2
      rw [hΦ] at hx
      obtain ⟨x', hx', hxx⟩ := hx
      rwa [Subtype.ext hxx] at hx'
    rcases eq_top_or_exists_le_coatom (⊥ : Subgroup ↥A) with h' | ⟨M, hM, -⟩
    · exact bot_ne_top h'
    · exact hM.1 (top_le_iff.mp (htop ▸ frattini_le_coatom hM))
  let PB : Subgroup G → Prop := fun B => Φ ≤ B ∧ B < A ∧ Γ ≤ Subgroup.normalizer (B : Set G)
  have hexB : ∃ n, ∃ B, PB B ∧ Nat.card A - Nat.card B = n :=
    ⟨_, Φ, ⟨le_rfl, hΦlt, hΓΦ⟩, rfl⟩
  obtain ⟨B, ⟨hΦB, hBA, hΓB⟩, hcardB⟩ := Nat.find_spec hexB
  have hmaxB : ∀ B', PB B' → B ≤ B' → B' = B := by
    intro B' hB' hBB'
    have h1 := hcardB ▸ Nat.find_min' hexB ⟨B', hB', rfl⟩
    have h2 : Nat.card B' ≤ Nat.card A := Subgroup.card_le_of_le hB'.2.1.le
    have h3 : Nat.card B ≤ Nat.card A := Subgroup.card_le_of_le hBA.le
    exact (Subgroup.eq_of_le_of_card_ge hBB' (by omega)).symm
  refine ⟨A, B, hAN, hBA, hΓA, hΓB, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have h1 := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (⟨a, ha⟩ : ↥A)
    exact hΦB (hΦ ▸ ⟨_, h1, rfl⟩)
  · intro a ha a' ha'
    have h1 : ⁅(⟨a, ha⟩ : ↥A), ⟨a', ha'⟩⁆ ∈ frattini ↥A :=
      CFSG.commutator_le_frattini_of_isPGroup (p := 2)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    exact hΦB (hΦ ▸ ⟨_, h1, by simp [commutatorElement_def]⟩)
  · intro J hBJ hJA hΓJ
    by_cases hJ : J = A
    · exact Or.inr hJ
    · exact Or.inl (hmaxB J ⟨hΦB.trans hBJ, lt_of_le_of_ne hJA hJ, hΓJ⟩ hBJ)
  · by_contra hc
    push Not at hc
    have hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ = b := by
      by_contra hKB
      push Not at hKB
      obtain ⟨k, hk, b, hb, hkb⟩ := hKB
      have h1 := hminA B ⟨hBA.le.trans hAN, hΓB, k, hk, b, hb, hkb⟩
      have h2 := Subgroup.card_lt_of_lt hBA
      omega
    exact hka₀ (conj_eq_of_perfect hKp (hA2.to_le hBA.le)
      (fun a ha b hb => (Subgroup.mem_normalizer_iff.mp (hΓB (hNΓ (hAN ha))) b).mp hb)
      hKB hc hk₀ ha₀)

theorem forall_comm_mem_of_isPGroup [Finite G] {Γ N A B : Subgroup G} (hN : IsPGroup 2 ↥N)
    (hNΓ : N ≤ Γ) (hΓN : Γ ≤ Subgroup.normalizer (N : Set G)) (hAN : A ≤ N) (hBA : B < A)
    (hΓA : Γ ≤ Subgroup.normalizer (A : Set G)) (hΓB : Γ ≤ Subgroup.normalizer (B : Set G))
    (hirr : ∀ J : Subgroup G, B ≤ J → J ≤ A → Γ ≤ Subgroup.normalizer (J : Set G) →
      J = B ∨ J = A) :
    ∀ q ∈ N, ∀ a ∈ A, q * a * q⁻¹ * a⁻¹ ∈ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconjB : ∀ g ∈ Γ, ∀ b ∈ B, g * b * g⁻¹ ∈ B := fun g hg b hb =>
    (Subgroup.mem_normalizer_iff.mp (hΓB hg) b).mp hb
  have hconjA : ∀ g ∈ Γ, ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun g hg a ha =>
    (Subgroup.mem_normalizer_iff.mp (hΓA hg) a).mp ha
  have hconjN : ∀ g ∈ Γ, ∀ q ∈ N, g * q * g⁻¹ ∈ N := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hΓN hg) q).mp hq
  let J : Subgroup G :=
    { carrier := {a | a ∈ A ∧ ∀ q ∈ N, q * a * q⁻¹ * a⁻¹ ∈ B}
      mul_mem' := by
        rintro a a' ⟨ha, h⟩ ⟨ha', h'⟩
        refine ⟨A.mul_mem ha ha', fun q hq => ?_⟩
        have e : q * (a * a') * q⁻¹ * (a * a')⁻¹ =
            (q * a * q⁻¹ * a⁻¹) * (a * (q * a' * q⁻¹ * a'⁻¹) * a⁻¹) := by group
        rw [e]
        exact B.mul_mem (h q hq) (hconjB a (hNΓ (hAN ha)) _ (h' q hq))
      one_mem' := ⟨A.one_mem, fun q _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, h⟩
        refine ⟨A.inv_mem ha, fun q hq => ?_⟩
        have e : q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ = a⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have h1 := hconjB a⁻¹ (hNΓ (hAN (A.inv_mem ha))) _ (B.inv_mem (h q hq))
        rwa [inv_inv] at h1 }
  have hBJ : B ≤ J := fun b hb => ⟨hBA.le hb, fun q hq =>
    B.mul_mem (hconjB q (hNΓ hq) b hb) (B.inv_mem hb)⟩
  have hJA : J ≤ A := fun a ha => ha.1
  have hΓJ : Γ ≤ Subgroup.normalizer (J : Set G) := by
    refine le_normalizer_of_conj fun g hg a ha => ⟨hconjA g hg a ha.1, fun q hq => ?_⟩
    have h1 := hconjB g hg _ (ha.2 (g⁻¹ * q * g) (by
      have := hconjN g⁻¹ (Γ.inv_mem hg) q hq
      rwa [inv_inv] at this))
    have e : g * ((g⁻¹ * q * g) * a * (g⁻¹ * q * g)⁻¹ * a⁻¹) * g⁻¹ =
        q * (g * a * g⁻¹) * q⁻¹ * (g * a * g⁻¹)⁻¹ := by group
    rwa [e] at h1
  have hJB : J ≠ B := by
    intro hJ
    have hBN : (B.subgroupOf N).Normal := ⟨fun b hb q => by
      rw [Subgroup.mem_subgroupOf] at hb ⊢
      exact hconjB q (hNΓ q.2) b hb⟩
    have hAN' : (A.subgroupOf N).Normal := ⟨fun a ha q => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      exact hconjA q (hNΓ q.2) a ha⟩
    set π := QuotientGroup.mk' (B.subgroupOf N) with hπ
    have hQ : IsPGroup 2 (↥N ⧸ B.subgroupOf N) := hN.to_quotient _
    have : Group.IsNilpotent (↥N ⧸ B.subgroupOf N) := hQ.isNilpotent
    have hn : ((A.subgroupOf N).map π).Normal :=
      Subgroup.Normal.map hAN' π (QuotientGroup.mk'_surjective _)
    have hne : (A.subgroupOf N).map π ≠ ⊥ := by
      obtain ⟨a, ha, haB⟩ := IsConcreteLE.exists_of_lt hBA
      intro h
      have h1 : π ⟨a, hAN ha⟩ ∈ (A.subgroupOf N).map π := ⟨⟨a, hAN ha⟩, ha, rfl⟩
      rw [h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at h1
      exact haB h1
    obtain ⟨⟨x, hxA, hxc⟩, hx1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨a, ha, rfl⟩ := hxA
    replace ha : (a : G) ∈ A := ha
    have haJ : (a : G) ∈ J := by
      refine ⟨ha, fun q hq => ?_⟩
      have h1 := Subgroup.mem_center_iff.mp hxc (π ⟨q, hq⟩)
      rw [hπ, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      have h2 := hconjB (q * a) (hNΓ (N.mul_mem hq a.2)) _ (B.inv_mem h1)
      have e2 : (q * a : G) * ((((⟨q, hq⟩ * a)⁻¹ * (a * ⟨q, hq⟩) : ↥N) : G))⁻¹ * (q * a)⁻¹ =
          q * a * q⁻¹ * a⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rwa [e2] at h2
    apply hx1'
    rw [hJ] at haJ
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact haJ
  rcases hirr J hBJ hJA hΓJ with h | h
  · exact absurd h hJB
  · intro q hq a ha
    have haJ : a ∈ J := h ▸ ha
    exact haJ.2 q hq

end L4316

namespace L4316

variable {F : Type} [Field F]

@[expose] def tvGL (t : Matrix.TransvectionStruct (Fin 3) F) : GL (Fin 3) F :=
  ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩

theorem coe_tvGL (t : Matrix.TransvectionStruct (Fin 3) F) :
    ((tvGL t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = t.toMatrix := rfl

theorem tvGL_mul_self [CharP F 2] (t : Matrix.TransvectionStruct (Fin 3) F) :
    tvGL t * tvGL t = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_tvGL, Units.val_one, Matrix.TransvectionStruct.toMatrix,
    Matrix.transvection_mul_transvection_same _ _ t.hij, CharTwo.add_self_eq_zero,
    Matrix.transvection_zero]

theorem eq_one_of_commute_tvGL [CharP F 2] (x : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
    (h : ∀ t : Matrix.TransvectionStruct (Fin 3) F,
      x * (QuotientGroup.mk (tvGL t) : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) =
        QuotientGroup.mk (tvGL t) * x) : x = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have key : ∀ t : Matrix.TransvectionStruct (Fin 3) F,
      Commute t.toMatrix (g : Matrix (Fin 3) (Fin 3) F) := by
    intro t
    have h1 := h t
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    set s := Matrix.GeneralLinearGroup.scalar (Fin 3) c with hs
    have hsc : s ∈ Subgroup.center (GL (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    set T := tvGL t with hT
    have hTT : T * T = 1 := tvGL_mul_self t
    have e1 : T * g = g * T * s := by
      rw [hc]
      group
    have e2 : T * g * T = g * s := by
      calc T * g * T = g * T * s * T := by rw [e1]
        _ = g * T * T * s := by
          rw [mul_assoc (g * T) s T, (Subgroup.mem_center_iff.mp hsc T).symm]
          group
        _ = g * s := by rw [mul_assoc g T T, hTT, mul_one]
    have e3 : s * s = 1 := by
      have : g = g * s * s := by
        calc g = T * T * g * (T * T) := by rw [hTT, one_mul, mul_one]
          _ = T * (T * g * T) * T := by group
          _ = T * (g * s) * T := by rw [e2]
          _ = T * g * T * s := by
            rw [mul_assoc T (g * s) T, mul_assoc g s T,
              (Subgroup.mem_center_iff.mp hsc T).symm]
            group
          _ = g * s * s := by rw [e2]
      have h2 : g * (s * s) = g * 1 := by rw [mul_one, ← mul_assoc, ← this]
      exact mul_left_cancel h2
    have hc1 : c = 1 := by
      have h2 : Matrix.GeneralLinearGroup.scalar (Fin 3) (c * c) = 1 := by
        rw [map_mul]
        exact e3
      have h3 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h2
      simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, Units.val_one] at h3
      have h4 : ((c : F) * c) = 1 := by simpa using h3
      have h5 : ((c : F) - 1) ^ 2 = 0 := by
        have h22 : (2 : F) = 0 := CharTwo.two_eq_zero
        linear_combination h4 + (1 - (c : F)) * h22
      have h6 : (c : F) = 1 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
        exact sub_eq_zero.mp this
      exact Units.ext h6
    have e4 : T * g = g * T := by
      rw [e1, hs, hc1, map_one, mul_one]
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) e4
    simp only [Units.val_mul, hT, coe_tvGL] at this
    exact this
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct key
  rw [QuotientGroup.eq_one_iff]
  refine Subgroup.mem_center_iff.mpr fun h' => Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ← hr]
  exact (Matrix.scalar_commute r (fun r' => Commute.all r r') _).symm

end L4316

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem Γ_le_normalizer_KZ :
    KZ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (KZ : Set G) :=
  _root_.sup_le Subgroup.le_normalizer (s.Y_le_normalizer_ZS.trans s.KZ_normal)

theorem pow_three_mem_KZ (hm : m = 2) {γ : G} (hγ : γ ∈ KZ ⊔ Subgroup.zpowers y) :
    γ ^ 3 ∈ KZ := by
  have hYN : Subgroup.zpowers y ≤ Subgroup.normalizer (KZ : Set G) :=
    s.Y_le_normalizer_ZS.trans s.KZ_normal
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left KZ (Subgroup.zpowers y) hYN
  have hγ' : γ ∈ ((KZ : Set G) * (Subgroup.zpowers y : Set G)) := by
    rw [← hset]
    exact hγ
  obtain ⟨k, hk, w, hw, rfl⟩ := hγ'
  have hw3 : w ^ 3 = 1 := by
    have h1 := orderOf_dvd_of_mem_zpowers hw
    have h3 : 2 ^ m - 1 = 3 := by rw [hm]; norm_num
    rw [s.orderOf_y, h3] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hc : ∀ j : ℕ, w ^ j * k * (w ^ j)⁻¹ ∈ KZ := fun j =>
    (Subgroup.mem_normalizer_iff.mp (hYN (Subgroup.pow_mem _ hw j)) k).mp hk
  have e : (k * w) ^ 3 = k * (w ^ 1 * k * (w ^ 1)⁻¹) * (w ^ 2 * k * (w ^ 2)⁻¹) * w ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [e, hw3, mul_one]
  exact KZ.mul_mem (KZ.mul_mem hk (hc 1)) (hc 2)

variable {α' : ↥(KZ ⊔ Subgroup.zpowers y) →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}

theorem mem_KZ_of_sq_eq_one (hm : m = 2) (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ)
    {γ : ↥(KZ ⊔ Subgroup.zpowers y)} (h : α' γ * α' γ = 1) : (γ : G) ∈ KZ := by
  have h2 : ((γ * γ : ↥(KZ ⊔ Subgroup.zpowers y)) : G) ∈ KZ := by
    rw [← map_mul, hα'k] at h
    exact pCoreOf_le 2 KZ h
  have h3 := s.pow_three_mem_KZ hm γ.2
  have e : (γ : G) = (γ : G) ^ 3 * ((γ : G) * γ)⁻¹ := by group
  rw [e]
  exact KZ.mul_mem h3 (KZ.inv_mem (by simpa using h2))

theorem eq_one_of_commute_alpha (hm : m = 2) (hα's : Function.Surjective α')
    (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ)
    {x : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}
    (hx : ∀ γ : ↥(KZ ⊔ Subgroup.zpowers y), (γ : G) ∈ KZ → x * α' γ = α' γ * x) : x = 1 := by
  have : CharP F 2 := s.charP
  refine L4316.eq_one_of_commute_tvGL x fun t => ?_
  obtain ⟨γ, hγ⟩ := hα's (QuotientGroup.mk (L4316.tvGL t))
  have hsq : α' γ * α' γ = 1 := by
    rw [hγ, ← QuotientGroup.mk_mul, L4316.tvGL_mul_self, QuotientGroup.mk_one]
  rw [← hγ]
  exact hx γ (s.mem_KZ_of_sq_eq_one hm hα'k hsq)

theorem exists_W (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2)
    (hZ : Subgroup.center (ModO2 KZ) = ⊥) (hα's : Function.Surjective α')
    (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ) :
    ∃ A B : Subgroup G, A ≤ pCoreOf 2 KZ ∧ B < A ∧
      KZ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set G) ∧
      KZ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (B : Set G) ∧ (∀ a ∈ A, a ^ 2 ∈ B) ∧
      (∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) ∧
      (∀ J : Subgroup G, B ≤ J → J ≤ A →
        KZ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (J : Set G) → J = B ∨ J = A) ∧
      (∀ γ : ↥(KZ ⊔ Subgroup.zpowers y),
        α' γ = 1 ↔ ∀ a ∈ A, (γ : G) * a * (γ : G)⁻¹ * a⁻¹ ∈ B) ∧
      ∃ k ∈ KZ, ∃ a ∈ A, k * a * k⁻¹ * a⁻¹ ∉ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pCoreOf 2 KZ with hN
  have hN2 : IsPGroup 2 ↥N := pCoreOf_isPGroup 2 KZ
  have hKΓ : KZ ≤ KZ ⊔ Subgroup.zpowers y := le_sup_left
  have hNΓ : N ≤ KZ ⊔ Subgroup.zpowers y := (pCoreOf_le 2 KZ).trans hKΓ
  have hΓN : KZ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (N : Set G) :=
    s.Γ_le_normalizer_KZ.trans (normalizer_le_normalizer_pCoreOf 2 KZ)
  have hKp : ⁅KZ, KZ⁆ = KZ := perfect_of_mem_cComp s.KZ_mem
  have hK : ∃ k ∈ KZ, ∃ q ∈ N, k * q * k⁻¹ ≠ q := by
    by_contra hc
    push Not at hc
    have hle : KZ ≤ N := by
      intro k hk
      refine s.charTwo_KZ ⟨hk, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      calc q * k = k * q * k⁻¹ * k := by rw [hc k hk q hq]
        _ = k * q := by group
    have h2 : IsPGroup 2 ↥KZ := hN2.to_le hle
    have : Group.IsNilpotent ↥KZ := h2.isNilpotent
    exact ne_bot_of_mem_cComp s.KZ_mem
      (CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hKp)
  obtain ⟨A, B, hAN, hBA, hΓA, hΓB, hsq, hcomm, hirr, k₀, hk₀, a₀, ha₀, hka₀⟩ :=
    L4316.exists_chief hN2 hNΓ hΓN hKp hK
  refine ⟨A, B, hAN, hBA, hΓA, hΓB, hsq, hcomm, hirr, fun γ => ?_, k₀, hk₀, a₀, ha₀, hka₀⟩
  have hNW := L4316.forall_comm_mem_of_isPGroup hN2 hNΓ hΓN hAN hBA hΓA hΓB hirr
  constructor
  · intro h
    exact hNW _ ((hα'k γ).mp h)
  · intro hγ
    have : Fact (B414.IsElem A B) := ⟨⟨hBA.le, hsq, hcomm⟩⟩
    obtain ⟨C, hCdef⟩ : ∃ C : Subgroup ↥(KZ ⊔ Subgroup.zpowers y),
        C = MonoidHom.ker (B414.secRep A B (KZ ⊔ Subgroup.zpowers y) hΓA hΓB) := ⟨_, rfl⟩
    have hCn : C.Normal := hCdef ▸ MonoidHom.normal_ker _
    have hmemC : ∀ δ : ↥(KZ ⊔ Subgroup.zpowers y),
        δ ∈ C ↔ ∀ a ∈ A, (δ : G) * a * (δ : G)⁻¹ * a⁻¹ ∈ B := by
      intro δ
      rw [hCdef, MonoidHom.mem_ker]
      exact B414.secRep_eq_one_iff A B (KZ ⊔ Subgroup.zpowers y) hΓA hΓB δ
    have hγC : γ ∈ C := (hmemC γ).mpr hγ
    have hq := s.quasisimple h135 hR hC h36 h37 h38 h39
    have hCK : ∀ δ : ↥(KZ ⊔ Subgroup.zpowers y), δ ∈ C → (δ : G) ∈ KZ → (δ : G) ∈ N := by
      set D : Subgroup ↥KZ := (C.map (KZ ⊔ Subgroup.zpowers y).subtype).subgroupOf KZ with hD
      have hDn : D.Normal := by
        refine ⟨fun d hd g => ?_⟩
        rw [hD, Subgroup.mem_subgroupOf] at hd ⊢
        obtain ⟨δ, hδ, hδe⟩ := hd
        have hδe' : (δ : G) = d := hδe
        have hg : (g : G) ∈ KZ ⊔ Subgroup.zpowers y := hKΓ g.2
        refine ⟨⟨g, hg⟩ * δ * (⟨g, hg⟩ : ↥(KZ ⊔ Subgroup.zpowers y))⁻¹, hCn.conj_mem δ hδ _, ?_⟩
        change ((⟨g, hg⟩ * δ * (⟨g, hg⟩ : ↥(KZ ⊔ Subgroup.zpowers y))⁻¹ :
          ↥(KZ ⊔ Subgroup.zpowers y)) : G) = ((g * d * g⁻¹ : ↥KZ) : G)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hδe']
      have hDm : (D.map (QuotientGroup.mk' (CFSG.pCore 2 ↥KZ))).Normal :=
        hDn.map _ (QuotientGroup.mk'_surjective _)
      rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
        (D.map (QuotientGroup.mk' (CFSG.pCore 2 ↥KZ))) with hc | htop
      · intro δ hδ hδK
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥KZ) ⟨δ, hδK⟩ ∈ Subgroup.center (ModO2 KZ) :=
          hc ⟨⟨δ, hδK⟩, by
            rw [hD, SetLike.mem_coe, Subgroup.mem_subgroupOf]
            exact ⟨δ, hδ, rfl⟩, rfl⟩
        rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact (mem_pCoreOf_iff' _).mpr h1
      · exfalso
        apply hka₀
        have hk₀C : (⟨k₀, hKΓ hk₀⟩ : ↥(KZ ⊔ Subgroup.zpowers y)) ∈ C := by
          obtain ⟨d, hd, hde⟩ := htop ▸ Subgroup.mem_top
            (QuotientGroup.mk' (CFSG.pCore 2 ↥KZ) ⟨k₀, hk₀⟩)
          rw [hD, SetLike.mem_coe, Subgroup.mem_subgroupOf] at hd
          obtain ⟨δ, hδ, hδe⟩ := hd
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hde
          have hn : ((d⁻¹ * ⟨k₀, hk₀⟩ : ↥KZ) : G) ∈ N := (mem_pCoreOf_iff' _).mpr hde
          have hnC : (⟨((d⁻¹ * ⟨k₀, hk₀⟩ : ↥KZ) : G), hNΓ hn⟩ :
              ↥(KZ ⊔ Subgroup.zpowers y)) ∈ C :=
            (hmemC _).mpr (hNW _ hn)
          have e : (⟨k₀, hKΓ hk₀⟩ : ↥(KZ ⊔ Subgroup.zpowers y)) =
              δ * ⟨((d⁻¹ * ⟨k₀, hk₀⟩ : ↥KZ) : G), hNΓ hn⟩ := by
            apply Subtype.ext
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [show (δ : G) = d from hδe]
            group
          rw [e]
          exact C.mul_mem hδ hnC
        exact (hmemC _).mp hk₀C a₀ ha₀
    refine s.eq_one_of_commute_alpha hm hα's hα'k fun δ hδK => ?_
    have hc : γ * δ * γ⁻¹ * δ⁻¹ ∈ C := by
      have h1 : δ * γ⁻¹ * δ⁻¹ ∈ C := hCn.conj_mem _ (C.inv_mem hγC) δ
      have e : γ * δ * γ⁻¹ * δ⁻¹ = γ * (δ * γ⁻¹ * δ⁻¹) := by group
      rw [e]
      exact C.mul_mem hγC h1
    have hcK : ((γ * δ * γ⁻¹ * δ⁻¹ : ↥(KZ ⊔ Subgroup.zpowers y)) : G) ∈ KZ := by
      have hγK : (γ : G) * δ * (γ : G)⁻¹ ∈ KZ :=
        (Subgroup.mem_normalizer_iff.mp (s.Γ_le_normalizer_KZ γ.2) δ).mp hδK
      simpa using KZ.mul_mem hγK (KZ.inv_mem hδK)
    have h1 : α' (γ * δ * γ⁻¹ * δ⁻¹) = 1 := (hα'k _).mpr (hCK _ hc hcK)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc α' γ * α' δ = α' γ * α' δ * (α' γ)⁻¹ * (α' δ)⁻¹ * (α' δ * α' γ) := by group
      _ = α' δ * α' γ := by rw [h1, one_mul]

end Setting4315

end CFSG.Quasithin.H13.Ch4
