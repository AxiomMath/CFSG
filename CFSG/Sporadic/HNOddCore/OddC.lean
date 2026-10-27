module

public import CFSG.Sporadic.HNOddCore.OddB
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2091
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native Equiv
open CFSG.ComponentClassification.SmallLocal

theorem sub_smul_comm {G α : Type*} [Group G] {H : Subgroup G} [MulAction H α] {a b : H}
    (h : a * b = b * a) (x : α) : a • (b • x) = b • (a • x) := by
  rw [← mul_smul, h, mul_smul]

theorem sub_eq_one_of_coe {G : Type*} [Group G] {H : Subgroup G} {L : Subgroup H} {l : L}
    (h : (l : H) = 1) : l = 1 :=
  Subtype.ext h

theorem isSimpleGroup_subgroupOf {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (hs : IsSimpleGroup H) : IsSimpleGroup (H.subgroupOf K) :=
  (Subgroup.subgroupOfEquivOfLe h).isSimpleGroup_congr.2 hs

theorem comm_of_conjNormal_eq {G0 : Type*} [Group G0] {J : Subgroup G0} {H : Subgroup J}
    {L : Subgroup H} [L.Normal] {g : H} (hg : MulAut.conjNormal (H := L) g = 1) (l : L) :
    (g : J) * ((l : H) : J) = ((l : H) : J) * (g : J) := by
  have e := DFunLike.congr_fun hg l
  have e2 := congrArg Subtype.val e
  rw [MulAut.conjNormal_apply, MulAut.one_apply] at e2
  have e3 : g * (l : H) = (l : H) * g := by
    calc g * (l : H) = g * (l : H) * g⁻¹ * g := by group
      _ = (l : H) * g := by rw [e2]
  exact sub_coe_comm e3

theorem card_mulAut_le {L : Type*} [Group L] [Finite L] {a b : L}
    (h : Subgroup.closure {a, b} = ⊤) : Nat.card (MulAut L) ≤ Nat.card L ^ 2 := by
  have hinj : Function.Injective (fun φ : MulAut L => (φ a, φ b)) := by
    intro φ ψ hφψ
    simp only [Prod.mk.injEq] at hφψ
    have e := MonoidHom.eq_of_eqOn_dense h (f := φ.toMonoidHom) (g := ψ.toMonoidHom) (by
      intro x hx
      rcases hx with rfl | rfl
      · exact hφψ.1
      · exact hφψ.2)
    exact MulEquiv.ext fun x => DFunLike.congr_fun e x
  calc Nat.card (MulAut L) ≤ Nat.card (L × L) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card L ^ 2 := by rw [Nat.card_prod, pow_two]

theorem dvd_25_cases {x : ℕ} (h : x ∣ 25) : x = 1 ∨ x = 5 ∨ x = 25 := by
  have hx : x ≤ 25 := Nat.le_of_dvd (by norm_num) h
  revert h
  interval_cases x <;> decide

theorem exists_closure_pair {L : Type*} [Group L] [Finite L]
    (h : Nat.card L ∣ 25 ∨ Nat.card L = 11) : ∃ a b : L, Subgroup.closure {a, b} = ⊤ := by
  by_cases htriv : ∀ x : L, x = 1
  · refine ⟨1, 1, eq_top_iff.2 fun x _ => ?_⟩
    rw [htriv x]
    exact Subgroup.one_mem _
  push Not at htriv
  obtain ⟨a, ha⟩ := htriv
  set A := Subgroup.closure ({a} : Set L) with hA
  have haA : a ∈ A := Subgroup.subset_closure rfl
  have hA1 : Nat.card A ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one.1 h1] at haA
    exact ha ((Subgroup.mem_bot).1 haA)
  have hAL : Nat.card A ∣ Nat.card L := Subgroup.card_subgroup_dvd_card A
  by_cases hAtop : A = ⊤
  · refine ⟨a, a, ?_⟩
    rw [Set.pair_eq_singleton]
    exact hAtop
  obtain ⟨b, hb⟩ : ∃ b, b ∉ A := by
    by_contra hcon
    push Not at hcon
    exact hAtop (eq_top_iff.2 fun x _ => hcon x)
  set B := Subgroup.closure ({a, b} : Set L) with hB
  have hAB : A ≤ B := Subgroup.closure_mono (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Set.mem_insert _ _)
  have hbB : b ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hABdvd : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le hAB
  have hBL : Nat.card B ∣ Nat.card L := Subgroup.card_subgroup_dvd_card B
  have hAB' : Nat.card A ≠ Nat.card B := by
    intro e
    have : A = B := Subgroup.eq_of_le_of_card_ge hAB (le_of_eq e.symm)
    rw [← this] at hbB
    exact hb hbB
  have hAneL : Nat.card A ≠ Nat.card L := fun e => hAtop ((Subgroup.card_eq_iff_eq_top A).1 e)
  refine ⟨a, b, (Subgroup.card_eq_iff_eq_top B).1 ?_⟩
  rcases h with h | h
  · rcases dvd_25_cases h with hL | hL | hL
    · rw [hL] at hAL
      exact absurd (Nat.dvd_one.1 hAL) hA1
    · rw [hL] at hAL hAneL
      have := (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hAL
      omega
    · rw [hL] at hAL hAneL hBL ⊢
      rcases dvd_25_cases hAL with h1 | h1 | h1
      · exact absurd h1 hA1
      · rcases dvd_25_cases hBL with h2 | h2 | h2
        · rw [h1, h2] at hABdvd
          exact absurd hABdvd (by norm_num)
        · rw [h1, h2] at hAB'
          exact absurd rfl hAB'
        · exact h2
      · exact absurd h1 hAneL
  · rw [h] at hAL hAneL
    have := (Nat.dvd_prime (by norm_num : Nat.Prime 11)).1 hAL
    omega

theorem exists_small_normal {C : Type*} [Group C] [Finite C] {N : Subgroup C} [N.Normal]
    (hN : N ≠ ⊥) (hdvd : Nat.card N ∣ 275) :
    ∃ L : Subgroup C, L.Normal ∧ L ≤ N ∧ L ≠ ⊥ ∧ (Nat.card L ∣ 25 ∨ Nat.card L = 11) := by
  by_cases h11 : 11 ∣ Nat.card N
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 11 N))
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hidx := (P : Subgroup N).card_mul_index
    have hnd : ¬ 11 ∣ (P : Subgroup N).index := P.not_dvd_index
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · rw [hk, pow_zero, one_mul] at hidx
          rw [hidx] at hnd
          exact absurd h11 hnd
        · rfl
      · exfalso
        have h1 : 11 ^ 2 ∣ Nat.card N := by
          rw [← hidx, hk]
          exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 11 hk2) _
        have := h1.trans hdvd
        exact absurd this (by norm_num)
    rw [hk1, pow_one] at hk
    have hidx25 : (P : Subgroup N).index ∣ 25 := by
      rw [hk] at hidx
      have : 11 * (P : Subgroup N).index ∣ 11 * 25 := by rw [hidx]; exact hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hcardS : Nat.card (Sylow 11 N) = 1 := by
      have h1 := Sylow.card_dvd_index P
      have h2 := card_sylow_modEq_one 11 N
      rcases dvd_25_cases (h1.trans hidx25) with h | h | h
      · exact h
      · rw [h] at h2
        exact absurd h2 (by decide)
      · rw [h] at h2
        exact absurd h2 (by decide)
    have : Subsingleton (Sylow 11 N) := (Nat.card_eq_one_iff_unique.1 hcardS).1
    have : (P : Subgroup N).Characteristic := Sylow.characteristic_of_subsingleton P
    refine ⟨(P : Subgroup N).map N.subtype, inferInstance, Subgroup.map_subtype_le _, ?_, Or.inr ?_⟩
    · intro hbot
      have := congrArg (fun K : Subgroup C => Nat.card K) hbot
      simp only [Subgroup.card_bot] at this
      rw [Subgroup.card_map_of_injective N.subtype_injective, hk] at this
      exact absurd this (by norm_num)
    · rw [Subgroup.card_map_of_injective N.subtype_injective, hk]
  · refine ⟨N, inferInstance, le_rfl, hN, Or.inl ?_⟩
    have hcop : Nat.Coprime (Nat.card N) 11 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h11))
    exact hcop.dvd_of_dvd_mul_right (by rw [show 25 * 11 = 275 from rfl]; exact hdvd)

abbrev C2 :
    Subgroup JH := Subgroup.centralizer {t2J}

theorem t2J_fix_x0 :
    t2J • x0 = x0 := (mem_HJ_iff_fix _).1 t2H.2

theorem N2_free
    {n : C2} (hn : n ∈ CFSG.oddCore C2) {p : X} (hp : t2J • p = p)
    (hfix : n • p = p) : n = 1 := by
  obtain ⟨-, -, -, -, -, hcore⟩ := stabilizer_t2 hp
  set S := MulAction.stabilizer C2 p
  have hnS : n ∈ S := hfix
  have hdvd : Nat.card ((CFSG.oddCore C2).subgroupOf S) ∣ Nat.card (CFSG.oddCore C2) := by
    rw [← Subgroup.card_map_of_injective S.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : (CFSG.oddCore C2).subgroupOf S ≤ CFSG.oddCore S :=
    le_oddCore_of_normal_odd (Subgroup.Normal.subgroupOf inferInstance S)
      (odd_card_oddCore.of_dvd_nat hdvd)
  have hmem : (⟨n, hnS⟩ : S) ∈ CFSG.oddCore S := hle (Subgroup.mem_subgroupOf.2 hn)
  rw [hcore, Subgroup.mem_bot] at hmem
  have := congrArg Subtype.val hmem
  exact this

@[expose] def Om2 :
    SubMulAction C2 X where
  carrier := {p | t2J • p = p}
  smul_mem' c p hp := by
    have hp' : t2J • p = p := hp
    have hc : (c : JH) * t2J = t2J * c := sub_mem_centralizer_iff.1 c.2
    show t2J • ((c : JH) • p) = (c : JH) • p
    rw [sub_smul_comm hc.symm, hp']

theorem card_Om2 :
    Nat.card Om2 = 8800 := by
  rw [← card_fix_t2]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [jR_smul]; rfl)

theorem card_N2_dvd :
    Nat.card (CFSG.oddCore C2) ∣ 8800 := by
  set N := CFSG.oddCore C2
  have hfree : ∀ ω : Om2, ∀ n : N, n • ω = ω → n = 1 := by
    intro ω n hn
    have h1 : (n : C2) • (ω : X) = ω := congrArg Subtype.val hn
    exact sub_eq_one_of_coe (N2_free n.2 ω.2 h1)
  have hstab : ∀ ω : Om2, MulAction.stabilizer N ω = ⊥ := fun ω =>
    eq_bot_iff.2 fun n hn => (Subgroup.mem_bot).2 (hfree ω n hn)
  have e : Om2 ≃ MulAction.orbitRel.Quotient N Om2 × N :=
    (MulAction.selfEquivSigmaOrbits N Om2).trans
      ((Equiv.sigmaCongrRight fun ω => (MulAction.orbitEquivQuotientStabilizer N _).trans
        ((Subgroup.quotientEquivOfEq (hstab _)).trans
          (QuotientGroup.quotientBot (G := N)).toEquiv)).trans (Equiv.sigmaEquivProd _ _))
  have h := Nat.card_congr e
  rw [Nat.card_prod] at h
  rw [← card_Om2, h]
  exact Dvd.intro_left _ rfl

theorem card_N2_dvd' :
    Nat.card (CFSG.oddCore C2) ∣ 275 := by
  have hodd : Odd (Nat.card (CFSG.oddCore C2)) := odd_card_oddCore
  have hcop : Nat.Coprime (Nat.card (CFSG.oddCore C2)) (2 ^ 5) :=
    Nat.Coprime.pow_right 5 (Nat.coprime_two_right.2 hodd)
  exact hcop.dvd_of_dvd_mul_right (by rw [show 275 * 2 ^ 5 = 8800 from rfl]; exact card_N2_dvd)

theorem A8_centralizes
    {L : Subgroup C2} [L.Normal] (hcard : Nat.card L ∣ 25 ∨ Nat.card L = 11)
    {a : JH} (ha : a ∈ A8J) (l : L) : a * ((l : C2) : JH) = ((l : C2) : JH) * a := by
  have hsimple : IsSimpleGroup (A8J.subgroupOf C2) :=
    isSimpleGroup_subgroupOf A8J_le_CJ_t2 A8J_simple
  have hcardA : Nat.card (A8J.subgroupOf C2) = 20160 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe A8J_le_CJ_t2).toEquiv, card_A8J]
  have : Finite (MulAut L) := Finite.of_injective (fun φ : MulAut L => (⇑φ : L → L))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  have hAut : Nat.card (MulAut L) < 20160 := by
    obtain ⟨x, y, hxy⟩ := exists_closure_pair hcard
    have h1 := card_mulAut_le hxy
    have h2 : Nat.card L ≤ 25 := by
      rcases hcard with h | h
      · exact Nat.le_of_dvd (by norm_num) h
      · omega
    have h3 : Nat.card L ^ 2 ≤ 25 ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  let φ : A8J.subgroupOf C2 →* MulAut L := MulAut.conjNormal.comp (A8J.subgroupOf C2).subtype
  have hker : φ.ker = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exfalso
      have hinj := (MonoidHom.ker_eq_bot_iff φ).1 h
      have := Nat.card_le_card_of_injective φ hinj
      omega
    · exact h
  have haC : a ∈ C2 := A8J_le_CJ_t2 ha
  have hmem : (⟨⟨a, haC⟩, ha⟩ : A8J.subgroupOf C2) ∈ φ.ker := by
    rw [hker]
    exact Subgroup.mem_top _
  rw [MonoidHom.mem_ker] at hmem
  exact comm_of_conjNormal_eq (g := ⟨a, haC⟩) hmem l

theorem oddCore_C2 :
    CFSG.oddCore C2 = ⊥ := by
  by_contra hN
  obtain ⟨L, hLn, hLN, hL1, hLcard⟩ := exists_small_normal hN card_N2_dvd'
  obtain ⟨l, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hL1
  have hlN : (l : C2) ∈ CFSG.oddCore C2 := hLN l.2
  have hlt2 : ((l : C2) : JH) * t2J = t2J * (l : C2) := sub_mem_centralizer_iff.1 (l : C2).2
  have hy : ((l : C2) : JH) • x0 ∈ {x : X | jR t2J • x = x ∧ ∀ g ∈ A8J, g • x = x} := by
    refine ⟨?_, fun g hg => ?_⟩
    · rw [jR_smul, sub_smul_comm hlt2.symm, t2J_fix_x0]
    · rw [sub_smul_comm (A8_centralizes hLcard hg l), (mem_HJ_iff_fix _).1 (A8J_le_HJ hg)]
  rw [fix_t2_A8] at hy
  have hfix : (l : C2) • x0 = x0 := hy
  exact hl1 (sub_eq_one_of_coe (N2_free hlN t2J_fix_x0 hfix))

end CFSG.Sporadic.HNOddCore
