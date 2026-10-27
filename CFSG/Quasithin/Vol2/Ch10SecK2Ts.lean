module

public import CFSG.Quasithin.Background.FFC4Five
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvField
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecK2Tb
public import CFSG.Quasithin.Vol2.Ch10SecK2Tm

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix

theorem card_sl2 (F : Type) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toEquiv,
    card_statedSL_two1527d]

theorem relIndex_le_of_realizesVia {V : Type*} [CommGroup V] {D : FFModel} [Finite ↥D.sec]
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    Z.relIndex U ≤ Nat.card ↥D.sec := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hk : Z.subgroupOf U = β.ker := by
    ext u
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hβk]
  have h1 : Z.relIndex U = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
    rw [Subgroup.relIndex, hk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hβs,
      Subgroup.card_top]
  rw [h1]
  exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)

theorem exists_not_mem_of_realizesVia {V : Type*} [CommGroup V] {D : FFModel}
    {H : Subgroup (MulAut V)} {Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H ⊤ Z π)
    {m : D.Amb} (hm : m ∈ D.sec) (hmk : m ∉ D.ker) : ∃ w : V, w ∉ Z := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  refine ⟨u, fun huZ => hmk ?_⟩
  have h1 := (hβk u).2 huZ
  rw [hu, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem ne_bot_of_exists {Γ : Type} [Group Γ] {V₁ : Subgroup Γ} {Z : Subgroup ↥V₁}
    (h : ∃ w : ↥V₁, w ∉ Z) : V₁ ≠ ⊥ := by
  rintro rfl
  obtain ⟨w, hw⟩ := h
  apply hw
  have : w = 1 := Subtype.ext (Subgroup.mem_bot.mp w.2)
  rw [this]
  exact Z.one_mem

theorem card_hermSub_le {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} (ha : 1 ≤ a)
    (hF : Nat.card F = 2 ^ (2 * a)) : Nat.card ↥(hermSub a (Fin 2) F) ≤ 2 ^ (4 * a) := by
  set P := {x : F // x ^ 2 ^ a = x}
  have hmem : ∀ X : ↥(hermSub a (Fin 2) F), ∀ i j,
      (Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) F))) j i =
        (Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) F))) i j ^ 2 ^ a := by
    intro X i j
    have h := X.2
    change (frobPow a (Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) F))))ᵀ =
      Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) F)) at h
    have := congrFun (congrFun h j) i
    rw [Matrix.transpose_apply] at this
    exact this.symm
  let f : ↥(hermSub a (Fin 2) F) → P × P × F := fun X =>
    let M := Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (⟨M 0 0, (hmem X 0 0).symm⟩, ⟨M 1 1, (hmem X 1 1).symm⟩, M 0 1)
  have hf : Function.Injective f := by
    intro X Y hXY
    simp only [f, Prod.mk.injEq] at hXY
    obtain ⟨h00, h11, h01⟩ := hXY
    have h00' := congrArg Subtype.val h00
    have h11' := congrArg Subtype.val h11
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00'
    · exact h01
    · simp only [Fin.mk_one, Fin.zero_eta]
      rw [hmem X 0 1, hmem Y 0 1, h01]
    · exact h11'
  have : Finite P := Subtype.finite
  have hP : Nat.card P ≤ 2 ^ a :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.InvField.card_pow_eq_self_le
      (Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num))
  calc Nat.card ↥(hermSub a (Fin 2) F) ≤ Nat.card (P × P × F) := Nat.card_le_card_of_injective f hf
    _ = Nat.card P * (Nat.card P * Nat.card F) := by rw [Nat.card_prod, Nat.card_prod]
    _ ≤ 2 ^ a * (2 ^ a * 2 ^ (2 * a)) := by
        rw [hF]
        exact Nat.mul_le_mul hP (Nat.mul_le_mul_right _ hP)
    _ = 2 ^ (4 * a) := by rw [← pow_add, ← pow_add]; ring_nf

theorem relIndex_le_card {Γ : Type} [Group Γ] [Finite Γ] (C V₁ : Subgroup Γ) :
    (C ⊓ V₁).relIndex V₁ ≤ Nat.card ↥V₁ :=
  Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)

theorem sl2_ne_168 {n : ℕ} (hn : 2 ≤ n) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 168 := by
  intro h
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    norm_num at h
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
    omega

theorem relIndex_centralizer_le {Γ : Type} [Group Γ] [Finite Γ] {L V₁ : Subgroup Γ}
    (hmod : ModCase L V₁) {n : ℕ} (hn : 1 < n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    V₁ ≠ ⊥ ∧ (Subgroup.centralizer (L : Set Γ) ⊓ V₁).relIndex V₁ ≤ (2 ^ n) ^ 2 := by
  have hcardL : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_sl2, hF]
  have hFK : ∀ {K : Type} [Field K] [Finite K],
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K) →
      Nat.card K = 2 ^ n := by
    intro K _ _ ⟨eK⟩
    rw [← hF]
    refine eq_of_card_sl2 Nat.card_pos Nat.card_pos ?_
    rw [← card_sl2, ← card_sl2, ← Nat.card_congr eK.toEquiv, Nat.card_congr e.toEquiv]
  obtain ⟨_, ⟨n', -, ⟨K, _, _, hK, eK⟩, ⟨K'', _, _, hK'', π, hπ⟩⟩ | ⟨⟨eA⟩, ⟨π, hπ⟩⟩ |
      ⟨⟨e3⟩, -⟩ | ⟨n', -, ⟨K, _, _, hK, eK⟩, ⟨K₂, _, _, _, hK₂, π, hπ⟩⟩ | ⟨⟨e3⟩, -⟩ |
      ⟨n', hSz, -⟩⟩ := hmod
  ·
    have hnn : n' = n :=
      Nat.pow_right_injective (le_refl 2) (show 2 ^ n' = 2 ^ n by rw [← hK, hFK eK])
    subst hnn
    have : Finite ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K'')).sec :=
      (inferInstance : Finite ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K''))))
    have h := relIndex_le_of_realizesVia hπ
    have hsec : Nat.card ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K'')).sec =
        Nat.card K'' ^ 2 := by
      show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K''))) = _
      rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]
    rw [Subgroup.relIndex_top_right, hsec, hK''] at h
    refine ⟨ne_bot_of_exists (exists_not_mem_of_realizesVia hπ
      (m := Multiplicative.ofAdd (fun _ => (1 : K''))) (Subgroup.mem_top _) ?_), ?_⟩
    · intro h1
      have h2 := congrFun (congrArg Multiplicative.toAdd (Subgroup.mem_bot.mp h1)) 0
      exact one_ne_zero h2
    · rw [Subgroup.inf_relIndex_right]
      exact h
  ·
    have h60 : 2 ^ n * ((2 ^ n) ^ 2 - 1) = 4 * (4 ^ 2 - 1) := by
      rw [← hcardL, Nat.card_congr eA.toEquiv, card_alternatingGroup1527d 5 (by norm_num)]
      decide
    have h4 : 2 ^ n = 4 := eq_of_card_sl2 Nat.one_le_two_pow (by norm_num) h60
    have : Finite ↥(FFModel.altDn 5).sec := (inferInstance : Finite ↥(G6.coreMod 5))
    have h := relIndex_le_of_realizesVia hπ
    rw [Subgroup.relIndex_bot_left, Subgroup.card_top] at h
    have h16 : Nat.card ↥(FFModel.altDn 5).sec = 16 := FFC.card_coreMod_five
    refine ⟨?_, by rw [h4]; exact (relIndex_le_card _ _).trans (h.trans h16.le)⟩
    by_contra hbot
    have hsk : ∀ x ∈ (FFModel.altDn 5).sec, x ∈ (FFModel.altDn 5).ker := by
      intro x hx
      by_contra hxk
      exact ne_bot_of_exists (exists_not_mem_of_realizesVia hπ hx hxk) hbot
    have hsq : (G6.allOnes 5) ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
      generalize Multiplicative.toAdd (G6.allOnes 5) i = c
      revert c
      decide
    have hle : Nat.card ↥(FFModel.altDn 5).sec ≤ 2 := by
      calc Nat.card ↥(FFModel.altDn 5).sec
          ≤ Nat.card ↥(Subgroup.zpowers (G6.allOnes 5)) :=
            Nat.card_le_card_of_injective (fun x => ⟨x.1, (hsk x.1 x.2).1⟩)
              (fun x y h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h'))
        _ = orderOf (G6.allOnes 5) := Nat.card_zpowers _
        _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hsq
    omega
  · exfalso
    apply sl2_ne_168 (show 2 ≤ n by omega)
    rw [← hcardL, Nat.card_congr e3.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  ·
    have hnn : 2 * n' = n :=
      Nat.pow_right_injective (le_refl 2) (show 2 ^ (2 * n') = 2 ^ n by rw [← hK, hFK eK])
    have : Finite ↥(FFModel.twistTensor n' (Assembly.LowTwoRank.StatedSL 2 K₂)).sec :=
      (inferInstance : Finite ↥(hermSub n' (Fin 2) K₂))
    have h := relIndex_le_of_realizesVia hπ
    rw [Subgroup.relIndex_bot_left, Subgroup.card_top] at h
    have hH := card_hermSub_le (F := K₂) (a := n') (by omega) hK₂
    refine ⟨ne_bot_of_exists (exists_not_mem_of_realizesVia hπ
      (m := Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K₂)) ?_ ?_), ?_⟩
    · change (frobPow n' (1 : Matrix (Fin 2) (Fin 2) K₂))ᵀ = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [frobPow]
    · intro h1
      have h2 := congrFun (congrFun (congrArg Multiplicative.toAdd (Subgroup.mem_bot.mp h1)) 0) 0
      change (1 : Matrix (Fin 2) (Fin 2) K₂) 0 0 = (0 : Matrix (Fin 2) (Fin 2) K₂) 0 0 at h2
      simp at h2
    · refine (relIndex_le_card _ _).trans (h.trans (hH.trans (le_of_eq ?_)))
      rw [← hnn, ← pow_mul]
      ring_nf
  · exfalso
    apply sl2_ne_168 (show 2 ≤ n by omega)
    rw [← hcardL, Nat.card_congr e3.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  ·
    exfalso
    apply Ch11.SecA.not_three_dvd_card_of_isSz hSz
    rw [hcardL]
    exact Dvd.dvd.mul_left three_dvd_sq_sub_one _

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
