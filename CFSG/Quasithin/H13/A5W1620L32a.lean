module

public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.Quasithin.H13.A5Z1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace L32

open CFSG.QuasithinUnique.Setup.Family

theorem statedSL_three_eq_top {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    CFSG.Assembly.LowTwoRank.StatedSL 3 F = ⊤ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  refine eq_top_iff.mpr fun A _ => Subgroup.subset_closure ?_
  show (A : Matrix (Fin 3) (Fin 3) F).det = 1
  have hne : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  have h := FiniteField.pow_card_sub_one_eq_one _ hne
  rwa [← Nat.card_eq_fintype_card, hF, show 2 - 1 = 1 from rfl, pow_one] at h

theorem nonempty_equiv_GL32 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nonempty (↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ≃* GL32) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  let φ : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hcard
  let e₁ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ≃* GL (Fin 3) F :=
    (MulEquiv.subgroupCongr (statedSL_three_eq_top hF)).trans Subgroup.topEquiv
  let e₂ : GL (Fin 3) F ≃* GL (Fin 3) (ZMod 2) :=
    Units.mapEquiv (φ.symm.mapMatrix.toMulEquiv)
  exact ⟨e₁.trans e₂⟩

theorem congr_conj {X Y : Type*} [Group X] [Group Y] (E : X ≃* Y) (c : X) :
    MulAut.congr E (MulAut.conj c) = MulAut.conj (E c) := by
  ext h
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_conj_of_pow_three {X : Type*} [Group X] (E : X ≃* GL32) (α : MulAut X)
    (hα : α ^ 3 = 1) : ∃ c : X, α = MulAut.conj c := by
  set β := MulAut.congr E α with hβdef
  have hβ : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  obtain ⟨g, hg⟩ :=
    Subgroup.sq_mem_of_index_two CFSG.LieType.SteinbergBR.AutGL32.index_inner β
  have hβ' : β = (β ^ 2)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    rw [pow_succ'] at hβ
    exact hβ
  refine ⟨E.symm g⁻¹, (MulAut.congr E).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply, ← hβdef, hβ', ← hg, map_inv]

theorem mul_three_of_sq {A : Type*} [CommGroup A] (w z₁ z₂ z₃ : A) (hw : w * w = 1) :
    (w * z₁) * (w * z₂) * (w * z₃) = w * (z₁ * z₂ * z₃) := by
  calc (w * z₁) * (w * z₂) * (w * z₃) = (w * w) * (w * (z₁ * z₂ * z₃)) := by ac_rfl
    _ = w * (z₁ * z₂ * z₃) := by rw [hw, one_mul]

end L32

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem Lv_le_of_mem {N : Subgroup G} (hQN : S.LvQ ≤ Subgroup.normalizer (N : Set G))
    {g : G} (hgN : g ∈ N) (hgL : g ∈ S.Lv) (hgQ : g ∉ S.LvQ) : S.Lv ≤ N := by
  obtain ⟨hgV, hgρ⟩ := S.rho_Lv hgL
  have hgρ' : S.frame.ρ ⟨g, hgV⟩ = c234 ∨ S.frame.ρ ⟨g, hgV⟩ = c234⁻¹ := by
    rcases hgρ with h | h | h
    · exact absurd (S.mem_LvQ.2 ⟨hgV, hgL, h⟩) hgQ
    · exact Or.inl h
    · exact Or.inr h
  have hdec : ∀ x ∈ S.Lv, ∃ i : ℕ, x * (g ^ i)⁻¹ ∈ S.LvQ := by
    intro x hx
    obtain ⟨hxV, hxρ⟩ := S.rho_Lv hx
    have hm : ∀ i : ℕ, x * (g ^ i)⁻¹ ∈ Subgroup.normalizer (V : Set G) := fun i =>
      Subgroup.mul_mem _ hxV (Subgroup.inv_mem _ (Subgroup.pow_mem _ hgV i))
    have hρi : ∀ i : ℕ, S.frame.ρ ⟨x * (g ^ i)⁻¹, hm i⟩ =
        S.frame.ρ ⟨x, hxV⟩ * (S.frame.ρ ⟨g, hgV⟩ ^ i)⁻¹ := by
      intro i
      have e : (⟨x * (g ^ i)⁻¹, hm i⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨x, hxV⟩ * (⟨g, hgV⟩ ^ i)⁻¹ := rfl
      rw [e, map_mul, map_inv, map_pow]
    have hLv : ∀ i : ℕ, x * (g ^ i)⁻¹ ∈ S.Lv := fun i =>
      S.Lv.mul_mem hx (S.Lv.inv_mem (S.Lv.pow_mem hgL i))
    have key : ∃ i : ℕ, S.frame.ρ ⟨x, hxV⟩ = S.frame.ρ ⟨g, hgV⟩ ^ i := by
      rcases hxρ with h | h | h <;> rcases hgρ' with h' | h' <;> rw [h, h']
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, (pow_one _).symm⟩
      · exact ⟨2, by decide⟩
      · exact ⟨2, by decide⟩
      · exact ⟨1, (pow_one _).symm⟩
    obtain ⟨i, hi⟩ := key
    refine ⟨i, S.mem_LvQ.2 ⟨hm i, hLv i, ?_⟩⟩
    rw [hρi i, hi, mul_inv_cancel]
  have hodd : ∀ x ∈ S.Lv, Odd (orderOf x) → x ∈ N := by
    intro x hx hxo
    obtain ⟨i, hi⟩ := hdec x hx
    set q := x * (g ^ i)⁻¹ with hq
    have hxq : x = q * g ^ i := by rw [hq, inv_mul_cancel_right]
    have hqN := hQN hi
    obtain ⟨j, hj⟩ := S.isPGroup_LvQ ⟨q, hi⟩
    have hj' : q ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hn : q * g ^ i * q⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hqN _).mp (N.pow_mem hgN i)
    have hxnq : x = (q * g ^ i * q⁻¹) * q := by rw [hxq]; group
    obtain ⟨n', hn', hpow⟩ := A4.exists_pow_mul_eq hn hqN (2 ^ j)
    have hxN : x ^ 2 ^ j ∈ N := by
      rw [hxnq, hpow, hj', mul_one]
      exact hn'
    refine B6.mem_of_pow_mem_of_coprime hxN ?_
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hxo)
  have hLv : S.Lv = oTwoRes (L ⊓ Subgroup.centralizer ({S.v12} : Set G)) := rfl
  intro x hx
  rw [hLv] at hx
  refine (Subgroup.closure_le N).mpr ?_ hx
  rintro y ⟨hy, m, hm, hym⟩
  have hyLv : y ∈ S.Lv := Subgroup.subset_closure ⟨hy, m, hm, hym⟩
  exact hodd y hyLv (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym))

theorem conj_mem_of_comm_mem {K B Q : Subgroup G} (hB : IsSylowTwoOf B K) (hQ : IsPGroup 2 ↥Q)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) {y : G} (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hcomm : ∀ t ∈ B, y * t * y⁻¹ * t⁻¹ ∈ Q) : ∀ t ∈ B, y * t * y⁻¹ ∈ B := by
  have hBK : B ≤ K := hB.1
  set Q₀ := Q ⊓ K with hQ₀
  have hBQ₀ : B ≤ Subgroup.normalizer (Q₀ : Set G) := by
    intro b hb
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ⟨?_, ?_⟩) fun x hx => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hBQ hb) x).mp hx.1
    · exact K.mul_mem (K.mul_mem (hBK hb) hx.2) (K.inv_mem (hBK hb))
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hBQ hb)) x).mp hx.1
      simpa using this
    · exact K.mul_mem (K.mul_mem (K.inv_mem (hBK hb)) hx.2) (hBK hb)
  have hQ₀2 : IsPGroup 2 ↥Q₀ := hQ.to_le inf_le_left
  have hsup2 : IsPGroup 2 ↥(Q₀ ⊔ B) := IsPGroup.to_sup_of_normal_left' hQ₀2 hB.2.1 hBQ₀
  have heq : B = Q₀ ⊔ B :=
    F1.eq_of_isSylowTwoOf_le hB (sup_le inf_le_right hBK) hsup2 le_sup_right
  have hQ₀B : Q₀ ≤ B := heq ▸ le_sup_left
  intro t ht
  have h1 : y * t * y⁻¹ * t⁻¹ ∈ Q₀ :=
    ⟨hcomm t ht, K.mul_mem ((Subgroup.mem_normalizer_iff.mp hyK t).mp (hBK ht))
      (K.inv_mem (hBK ht))⟩
  have e : y * t * y⁻¹ = (y * t * y⁻¹ * t⁻¹) * t := by group
  rw [e]
  exact B.mul_mem (hQ₀B h1) ht

end Setting

end CFSG.Quasithin.H13.A5
