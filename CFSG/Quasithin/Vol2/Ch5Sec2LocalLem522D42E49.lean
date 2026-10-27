module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoArr
public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.Open CFSG.Blueprint

@[expose] def e49WordH : List ℕ := [2, 13, 2, 1, 9, 1]

@[expose] def e49WordZ : List ℕ := [16, 17, 1, 9, 1, 17, 16, 1, 9, 1]

@[expose] def e49ArrH : Array GF8 :=
  (#[2, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0,
    0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
    5] : Array ℕ).map GF8.ofNat'

@[expose] def e49ArrZ : Array GF8 :=
  (#[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0,
    0] : Array ℕ).map GF8.ofNat'

@[expose] def e49ArrZ2 : Array GF8 :=
  (#[1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0,
    0, 1] : Array ℕ).map GF8.ofNat'

@[expose] def e49ArrZ4 : Array GF8 :=
  (#[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0] : Array ℕ).map GF8.ofNat'

@[expose] def e49DiagH : Fin 8 → GF8 :=
  ![GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 2,
    GF8.ofNat' 2, GF8.ofNat' 5]

theorem e49_check_h : wordArr e49WordH = e49ArrH := by
  decide +kernel

theorem e49_check_z : wordArr e49WordZ = e49ArrZ := by
  decide +kernel

theorem e49_check_z7 : mulArr e49ArrZ e49ArrZ = e49ArrZ2 ∧ mulArr e49ArrZ2 e49ArrZ2 = e49ArrZ4 ∧
    mulArr e49ArrZ4 (mulArr e49ArrZ2 e49ArrZ) = oneArr := by
  decide +kernel

theorem e49_check_comm : mulArr e49ArrH e49ArrZ = mulArr e49ArrZ e49ArrH := by
  decide +kernel

theorem e49_check_diag : toMat e49ArrH = Matrix.diagonal e49DiagH ∧ e49DiagH ^ 7 = 1 ∧
    e49DiagH 0 ≠ 1 ∧ toMat e49ArrZ 0 5 ≠ 0 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem elemAbelian_sup_of_commute {Q : Type*} [Group Q] [Finite Q] {a b : Q} (ha : a ^ 7 = 1)
    (ha1 : a ≠ 1) (hb : b ^ 7 = 1) (hab : a * b = b * a) (hbn : b ∉ Subgroup.zpowers a) :
    IsElemAbelian 7 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 49 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hb1 : b ≠ 1 := fun h => hbn (h ▸ one_mem _)
  have hoa : orderOf a = 7 := orderOf_eq_prime ha ha1
  have hob : orderOf b = 7 := orderOf_eq_prime hb hb1
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) ∣ 7 := by
      rw [← hob, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hbn
      have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hob])
      exact (heq ▸ inf_le_left : Subgroup.zpowers b ≤ Subgroup.zpowers a)
        (Subgroup.mem_zpowers b)
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoa, hob] at hcard
  have hz7 : ∀ c : Q, c ^ 7 = 1 → ∀ x ∈ Subgroup.zpowers c, x ^ 7 = 1 := by
    intro c hc x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]
  have hmem : ∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b,
      ∃ u ∈ Subgroup.zpowers a, ∃ v ∈ Subgroup.zpowers b, u * v = x := by
    intro x hx
    have hx' : x ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Q) : Set Q) := hx
    rw [hset] at hx'
    obtain ⟨u, hu, v, hv, huv⟩ := hx'
    exact ⟨u, hu, v, hv, huv⟩
  have hzc : ∀ c : Q, ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro c x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self c i j).eq
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, hcard⟩
  · obtain ⟨u, hu, v, hv, hx⟩ := hmem x x.2
    obtain ⟨u', hu', v', hv', hy⟩ := hmem y y.2
    change (x : Q) * y = y * x
    rw [← hx, ← hy]
    calc u * v * (u' * v') = (u * u') * (v * v') := by
          rw [mul_assoc, ← mul_assoc v, ← hcomm u' hu' v hv, mul_assoc, mul_assoc]
      _ = (u' * u) * (v' * v) := by rw [hzc a u hu u' hu', hzc b v hv v' hv']
      _ = u' * v' * (u * v) := by
          rw [mul_assoc, ← mul_assoc u, hcomm u hu v' hv', mul_assoc, mul_assoc]
  · obtain ⟨u, hu, v, hv, rfl⟩ := hmem x hx
    rw [(show Commute u v from hcomm u hu v hv).mul_pow, hz7 a ha u hu, hz7 b hb v hv, one_mul]

theorem exists_elemAbelian_49 {X : Type} [Group X]
    (hm : ChevalleyExceptionalModel X .trialityD4 2 1) :
    ∃ E : Subgroup X, IsElemAbelian 7 E ∧ Nat.card ↥E = 49 := by
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S63.nonempty_equiv_trialityGroup8 X
    (Or.inr (Or.inl ⟨rfl, by decide, hm⟩))
  set h : ↥trialityGroup8 := ⟨wordGL e49WordH, wordGL_mem _⟩ with hhdef
  set z : ↥trialityGroup8 := ⟨wordGL e49WordZ, wordGL_mem _⟩ with hzdef
  have hext : ∀ a b : ↥trialityGroup8, ((a : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
      ((b : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) → a = b :=
    fun a b hab => Subtype.ext (Units.ext hab)
  have hhM : ((h : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat e49ArrH := by
    rw [hhdef, coe_wordGL, e49_check_h]
  have hzM : ((z : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat e49ArrZ := by
    rw [hzdef, coe_wordGL, e49_check_z]
  obtain ⟨hdiag, hd7, hd0, hz05⟩ := e49_check_diag
  have hpowM : ∀ n : ℕ, (((h ^ n : ↥trialityGroup8) : GL (Fin 8) GF8) :
      Matrix (Fin 8) (Fin 8) GF8) = Matrix.diagonal (e49DiagH ^ n) := fun n => by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hhM, hdiag, Matrix.diagonal_pow]
  have hh7 : h ^ 7 = 1 := hext _ _ (by rw [hpowM, hd7]; simp)
  have hh1 : h ≠ 1 := fun h1 => hd0 (by
    have h2 := congrArg (fun a : ↥trialityGroup8 =>
      ((a : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) 0 0) h1
    simpa [hhM, hdiag] using h2)
  have hz7 : z ^ 7 = 1 := hext _ _ (by
    obtain ⟨h2, h4, h7⟩ := e49_check_z7
    have e2 : toMat e49ArrZ2 = toMat e49ArrZ ^ 2 := by rw [← h2, toMat_mulArr, sq]
    have e4 : toMat e49ArrZ4 = toMat e49ArrZ ^ 4 := by
      rw [← h4, toMat_mulArr, e2, ← pow_add]
    have e7 : toMat e49ArrZ ^ 7 = 1 := by
      rw [show (7 : ℕ) = 4 + (2 + 1) from rfl, pow_add, pow_add, pow_one, ← e4, ← e2,
        ← toMat_mulArr, ← toMat_mulArr, h7, oneArr, toMat_ofMat]
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hzM, e7]
    rfl)
  have hcomm : h * z = z * h := hext _ _ (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hhM, hzM,
      ← toMat_mulArr, ← toMat_mulArr, e49_check_comm])
  have hzn : z ∉ Subgroup.zpowers h := by
    intro hz
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
    have h2 := congrArg (fun a : ↥trialityGroup8 =>
      ((a : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) 0 5) hn
    simp only [hpowM, hzM] at h2
    rw [Matrix.diagonal_apply_ne _ (by decide)] at h2
    exact hz05 h2.symm
  obtain ⟨hE, hE49⟩ := elemAbelian_sup_of_commute hh7 hh1 hz7 hcomm hzn
  refine ⟨(Subgroup.zpowers h ⊔ Subgroup.zpowers z).map e.symm.toMonoidHom,
    CFSG.SectionRank.isElemAbelian_map hE _, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hE49]

end CFSG.Quasithin.H13.D42
