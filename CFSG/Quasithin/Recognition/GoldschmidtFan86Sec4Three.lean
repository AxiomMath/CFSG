module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ThreeAbs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4NoChar
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Fan28

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Open

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan41_3 (F : FanTree Γ G) : Fan41Three F := by
  intro a b c L hab hac hL h3 h28
  have hL' := hL
  obtain ⟨Lt, hLt, hle⟩ := fan41_max F hL
  set Ga := MulAction.stabilizer G a with hGa
  set Gb := MulAction.stabilizer G b with hGb
  set H : Subgroup G := Lt ⊓ Ga with hH
  set R : Subgroup G := H ⊓ Gb with hR
  obtain ⟨hfinH, htrH, hcardH, hR2⟩ := lamSet_setup F hab hLt.1
  have hHG : H ≤ Ga := inf_le_right
  have hRH : R ≤ H := inf_le_left
  rw [h3] at hcardH
  let e : ↥(R.subgroupOf H) ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRH
  have hP2 : IsPGroup 2 ↥(R.subgroupOf H) := hR2.of_equiv e.symm
  have hcardP : Nat.card ↥(R.subgroupOf H) = Nat.card ↥R := Nat.card_congr e.toEquiv
  have hcard : Nat.card ↥H = 3 * Nat.card ↥(R.subgroupOf H) := by rw [hcardP, hcardH]
  have hno : ∀ K : Subgroup ↥H, K ≤ R.subgroupOf H →
      (K.subgroupOf (R.subgroupOf H)).Characteristic → K.Normal → K = ⊥ :=
    fun K hK hchar hN => fan41_noChar_subtype F hab hac hLt K hK hchar hN
  let S : SubMulAction ↥H V :=
    ⟨Γ.neighborSet a, fun h x hx => F.adj_smul_of_mem_stabilizer (hHG h.2) hx⟩
  have hfinS : Finite ↥S := (F.ncard_neighborSet_le a).2.to_subtype
  let φ : ↥H →* Equiv.Perm ↥S := MulAction.toPermHom ↥H ↥S
  have hφ : ∀ (h : ↥H) (u : ↥S), (φ h u : V) = (h : G) • (u : V) := fun h u => rfl
  have hker : ∀ h : ↥H, h ∈ φ.ker ↔ (h : G) ∈ nbrStab Γ G a := by
    intro h
    constructor
    · intro hh w hw
      have := congrArg (fun σ : Equiv.Perm ↥S => (σ ⟨w, hw⟩ : V)) hh
      simpa [hφ] using this
    · intro hh
      refine Equiv.ext fun u => Subtype.ext ?_
      rw [hφ]
      exact hh _ u.2
  have hkerR : φ.ker ≤ R.subgroupOf H := by
    intro h hh
    have h1 := (hker h).1 hh
    exact ⟨h.2, MulAction.mem_stabilizer_iff.2 (h1 b hab)⟩
  have hcard3 : Nat.card ↥S = 3 := h3
  have hRne : R ≠ ⊥ := by
    obtain ⟨Q, hQ0, hQ, hLQ, -, -⟩ := hL
    intro hR0
    apply hQ0
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ L := by rw [hLQ]; exact Subgroup.le_normalizer hx
    have : x ∈ R := ⟨hle ⟨hxL, (hQ hx).1⟩, (hQ hx).2⟩
    rw [hR0] at this
    exact this
  have hR'ne : R.subgroupOf H ≠ ⊥ := by
    intro h
    apply hRne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hRH hx⟩ : ↥H) ∈ R.subgroupOf H := hx
    rw [h] at this
    have h1 : (⟨x, hRH hx⟩ : ↥H) = 1 := this
    exact congrArg Subtype.val h1
  have hkerne : φ.ker ≠ R.subgroupOf H := by
    intro heq
    have hN : (R.subgroupOf H).Normal := heq ▸ MonoidHom.normal_ker φ
    exact hR'ne (hno (R.subgroupOf H) le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance) hN)
  have hlt : Nat.card φ.ker < Nat.card ↥(R.subgroupOf H) := by
    by_contra hcon
    push Not at hcon
    exact hkerne (Subgroup.eq_of_le_of_card_ge hkerR hcon)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hkerR
  have hker0 : 0 < Nat.card φ.ker := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hcon
    push Not at hcon
    interval_cases k
    · rw [mul_zero] at hk
      exact absurd hk (Nat.card_pos (α := ↥(R.subgroupOf H))).ne'
    · rw [mul_one] at hk
      omega
  have hindex : φ.ker.index = 3 * k := by
    refine Nat.eq_of_mul_eq_mul_left hker0 ?_
    rw [Subgroup.card_mul_index, hcard, hk]
    ring
  have hrange : Nat.card ↥φ.range = 3 * k := by
    rw [← hindex]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
  have hperm : Nat.card (Equiv.Perm ↥S) = 6 := by
    rw [Nat.card_perm, hcard3]
    rfl
  have hle6 : Nat.card ↥φ.range ≤ 6 := hperm ▸ Subgroup.card_le_card_group _
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ (by omega)
  have hsyl : Nat.card ↥(R.subgroupOf H) = 2 ^ (Nat.card ↥H).factorization 2 := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hP2
    rw [hcard, hm, Nat.factorization_mul (by norm_num) (by positivity),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]
  let Syl : Sylow 2 ↥H := Sylow.ofCard (R.subgroupOf H) hsyl
  have hZ : pCore 2 ↥H ≤ R.subgroupOf H := by
    have : (pCore 2 ↥H).Normal := pCore_normal 2
    exact IsPGroup.le_sylow_of_normal (pCore_isPGroup 2) Syl
  have hcore : pCore 2 ↥H ≤ φ.ker := by
    intro z hz
    have hnormal : (pCore 2 ↥H).Normal := pCore_normal 2
    rw [hker]
    intro u hu
    obtain ⟨h, hh, hhb⟩ := htrH b u hab hu
    have hconj : (⟨h, hh⟩ : ↥H)⁻¹ * z * ⟨h, hh⟩ ∈ pCore 2 ↥H := by
      have := hnormal.conj_mem z hz (⟨h, hh⟩ : ↥H)⁻¹
      simpa using this
    have h1 : ((⟨h, hh⟩ : ↥H)⁻¹ * z * ⟨h, hh⟩ : ↥H) • b = b :=
      MulAction.mem_stabilizer_iff.1 (hZ hconj).2
    have h2 : h⁻¹ • ((z : G) • (h • b)) = b := by
      rw [← mul_smul, ← mul_smul]
      exact h1
    rw [← hhb]
    exact (inv_smul_eq_iff.1 h2)
  have hkerP : IsPGroup 2 φ.ker := hP2.to_le hkerR
  obtain ⟨eQ⟩ := nonempty_oTwoQuot_equiv φ hsurj hkerP hcore
  let eS : ↥S ≃ Fin 3 := (Finite.equivFin ↥S).trans (finCongr hcard3)
  have hQ3 : Nonempty (oTwoQuot ↥H ≃* Equiv.Perm (Fin 3)) := ⟨eQ.trans (Equiv.permCongrHom eS)⟩
  have hidxR : (R.subgroupOf H).index = 3 := by
    have : Nat.card ↥(R.subgroupOf H) * (R.subgroupOf H).index =
        Nat.card ↥(R.subgroupOf H) * 3 := by
      rw [Subgroup.card_mul_index, hcard, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos this
  have hsylow : IsSylowTwoOf (R.subgroupOf H) ⊤ := by
    refine ⟨le_top, hP2, ?_⟩
    show ¬ 2 ∣ (R.subgroupOf H).relIndex ⊤
    rw [Subgroup.relIndex_top_right, hidxR]
    norm_num
  obtain ⟨n, hn, C, hCg, hCf, hC2, ⟨eH⟩⟩ := h28 ↥H (R.subgroupOf H) hsylow hQ3
    (fun K hK hK0 hchar hN => hK0 (hno K hK hchar hN))
  obtain ⟨Q, hQ0, hQ, hLQ, -, -⟩ := hL
  have hQL : Q ≤ L := by rw [hLQ]; exact Subgroup.le_normalizer
  have hLaH : L ⊓ Ga ≤ H := hle
  have hQH : Q ≤ H := fun x hx => hLaH ⟨hQL hx, (hQ hx).1⟩
  have hN : Subgroup.normalizer ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H) =
      (L ⊓ Ga).subgroupOf H := by
    rw [← Subgroup.subgroupOf_normalizer_eq hQH, ← hLQ]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, hHG x.2⟩, fun h => h.1⟩
  let eL : ↥(Subgroup.normalizer ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H)) ≃* ↥(L ⊓ Ga) :=
    (MulEquiv.subgroupCongr hN).trans (Subgroup.subgroupOfEquivOfLe hLaH)
  let eQ' : ↥(Q.subgroupOf H) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQH
  have hQ2 : IsPGroup 2 ↥Q := (F.edge_two a b hab).to_le hQ
  have hQ'2 : IsPGroup 2 ↥(Q.subgroupOf H) := hQ2.of_equiv eQ'.symm
  have hQ'0 : Q.subgroupOf H ≠ ⊥ := by
    intro h
    apply hQ0
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hQH hx⟩ : ↥H) ∈ Q.subgroupOf H := hx
    rw [h] at this
    exact congrArg Subtype.val (show (⟨x, hQH hx⟩ : ↥H) = 1 from this)
  have h3dvd : 3 ∣ Nat.card ↥(Subgroup.normalizer ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H)) := by
    rw [Nat.card_congr eL.toEquiv]
    obtain ⟨-, -, hcardL, -⟩ := lamSet_setup F hab hL'
    rw [h3] at hcardL
    rw [hcardL]
    exact dvd_mul_right _ _
  obtain ⟨n', hn', C', hC'g, hC'f, hC'2, ⟨f⟩⟩ :=
    exists_mulEquiv_perm_prod hn hC2 eH hQ'0 hQ'2 h3dvd
  exact ⟨n', hn', C', hC'g, hC'f, hC'2, ⟨eL.symm.trans f⟩⟩

end CFSG.Quasithin.Fan86
