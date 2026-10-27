module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaBasic
public import CFSG.Quasithin.Background.D14Chief
public import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev str86UN (N L2 S : Subgroup G) : Subgroup G := conjClosure N (L2 ⊔ S)

abbrev str86U1 (P L2 S : Subgroup G) : Subgroup G := conjClosure P (L2 ⊔ S)

abbrev str86U2 (p N L2 S : Subgroup G) : Subgroup G := conjClosure p (L2 ⊔ S)

theorem str86U2_le_str86U1 {p P L2 S : Subgroup G} (hpP : p ≤ P) :
    str86U2 p P L2 S ≤ str86U1 P L2 S :=
  conjClosure_mono hpP le_rfl

theorem str86U1_le_str86UN {P N L2 S : Subgroup G} (hPN : P ≤ N) :
    str86U1 P L2 S ≤ str86UN N L2 S :=
  conjClosure_mono hPN le_rfl

theorem str86UN_normalizes {N L2 S : Subgroup G} :
    L2 ⊔ S ≤ Subgroup.normalizer (str86UN N L2 S : Set G) :=
  le_normalizer_conjClosure N (L2 ⊔ S)

theorem str86U1_normalizes {P L2 S : Subgroup G} :
    L2 ⊔ S ≤ Subgroup.normalizer (str86U1 P L2 S : Set G) :=
  le_normalizer_conjClosure P (L2 ⊔ S)

theorem str86U2_normalizes {p N L2 S : Subgroup G} :
    L2 ⊔ S ≤ Subgroup.normalizer (str86U2 p N L2 S : Set G) :=
  le_normalizer_conjClosure p (L2 ⊔ S)

theorem str86UN_le_str86U {L1 L2 S : Subgroup G} {N : Subgroup G}
    (hN : N ≤ Z1 L1 L2 S) : str86UN N L2 S ≤ str86U L1 L2 S :=
  conjClosure_mono hN le_rfl

theorem str86U1_le_str86U {L1 L2 S : Subgroup G} {P : Subgroup G}
    (hP : P ≤ Z1 L1 L2 S) : str86U1 P L2 S ≤ str86U L1 L2 S :=
  conjClosure_mono hP le_rfl

theorem str86U2_le_str86U {L1 L2 S : Subgroup G} {p : Subgroup G}
    (hp : p ≤ Z1 L1 L2 S) : str86U2 p p L2 S ≤ str86U L1 L2 S :=
  conjClosure_mono hp le_rfl

theorem str86UN_isNormalIn {L1 L2 S : Subgroup G} {N : Subgroup G} (hN : N ≤ Z1 L1 L2 S) :
    IsNormalIn (L2 ⊔ S) (str86U L1 L2 S) (str86UN N L2 S) :=
  ⟨str86UN_le_str86U hN, fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (str86UN_normalizes (N := N) hg) x).mp hx⟩

theorem str86U1_isNormalIn {L1 L2 S : Subgroup G} {P : Subgroup G} (hP : P ≤ Z1 L1 L2 S) :
    IsNormalIn (L2 ⊔ S) (str86U L1 L2 S) (str86U1 P L2 S) :=
  ⟨str86U1_le_str86U hP, fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (str86U1_normalizes (P := P) hg) x).mp hx⟩

theorem str86U2_isNormalIn {L1 L2 S : Subgroup G} {p : Subgroup G} (hp : p ≤ Z1 L1 L2 S) :
    IsNormalIn (L2 ⊔ S) (str86U L1 L2 S) (str86U2 p p L2 S) :=
  ⟨str86U2_le_str86U hp, fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (str86U2_normalizes (p := p) (N := p) hg) x).mp hx⟩

theorem str86U2_le_z2 {L1 L2 S : Subgroup G} {N p : Subgroup G}
    (hN : IsElemAbelian 2 N) (hNZ : N ≤ Z1 L1 L2 S)
    (hp : p = N ⊓ Subgroup.centralizer (S : Set G))
    (hQ2S : Q2 L1 L2 S ≤ S)
    (hQ2H : L2 ⊔ S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G))
    (hZ1Q2 : Z1 L1 L2 S ≤ Q2 L1 L2 S) :
    str86U2 p p L2 S ≤ Z2 L1 L2 S := by
  classical
  have hkey : ∀ g ∈ L2 ⊔ S, ∀ y ∈ p, g * y * g⁻¹ ∈ Z2 L1 L2 S := by
    intro g hg y hy
    rw [hp] at hy
    obtain ⟨hyN, hyC⟩ := Subgroup.mem_inf.mp hy
    have hsq : y * y = 1 := by
      have := hN.2 y hyN
      simpa [pow_two] using this
    have hmemU : g * y * g⁻¹ ∈ str86U L1 L2 S :=
      mem_conjClosure hg (hNZ hyN)
    have hmemQ2 : g * y * g⁻¹ ∈ Q2 L1 L2 S :=
      conjClosure_le (fun h hh z hz => (Subgroup.mem_normalizer_iff.mp (hQ2H hh) z).mp
        (hZ1Q2 hz)) hmemU
    have hmemC : g * y * g⁻¹ ∈ Subgroup.centralizer (Q2 L1 L2 S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hq : g⁻¹ * z * g ∈ Q2 L1 L2 S := by
        have := (Subgroup.mem_normalizer_iff.mp (hQ2H (Subgroup.inv_mem _ hg)) z).mp hz
        simpa using this
      have hqS : g⁻¹ * z * g ∈ S := hQ2S hq
      have hcomm : y * (g⁻¹ * z * g) = (g⁻¹ * z * g) * y :=
        (Subgroup.mem_centralizer_iff.mp hyC _ hqS).symm
      calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * y * g⁻¹) * z := by group
    have hsq' : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
      calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hsq]; group
    exact mem_omegaOneCenterOf hmemQ2 (Subgroup.mem_centralizer_iff.mp hmemC)
      (by rw [pow_two]; exact hsq')
  refine conjClosure_le ?_
  intro g hg y hy
  exact hkey g hg y hy

theorem str86H_eq_oTwoUpper_sup_s {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) :
    oTwoUpper (L2 ⊔ S) ⊔ S = L2 ⊔ S := by
  classical
  let H : Subgroup G := L2 ⊔ S
  let Q : Subgroup G := Q2 L1 L2 S
  have hS2 : S = (S ⊓ L2) ⊔ Q := by
    simpa [Q] using eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hQS : Q ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : H = L2 ⊔ Q := by
    show L2 ⊔ S = L2 ⊔ Q
    rw [sup_eq_of_S_eq_right hS2]
  have hpCore : pCoreOf 2 H = Q := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q, Q1, Q2, P1, P2, bigB_comm] using h
  have hL2H : IsL2Quot m (oTwoQuot ↥H) := by
    obtain ⟨eL2⟩ := hL2
    have hQ12 : L2 ⊔ Q1 L2 L1 S = L2 ⊔ Q2 L1 L2 S := by
      rw [Q1, Q2, P1, P2, bigB_comm]
    rw [hsup2, ← hQ12]
    exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL2⟩
  have hsupQ : oTwoUpper H ⊔ Q = H := by
    have hperf : Group.IsPerfect (oTwoQuot ↥H) := isPerfect_of_isL2Quot hm hL2H
    let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
    have htop : oTwoUpper (⊤ : Subgroup (oTwoQuot ↥H)) = ⊤ :=
      C2Nine.oTwoUpper_eq_of_perfect (Subgroup.commutator_eq_self (H := ⊤))
    have hmap := oTwoUpper_map (G' := oTwoQuot ↥H) π (⊤ : Subgroup ↥H)
    rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective π hsurj, htop] at hmap
    have hKtop : Subgroup.map π (oTwoUpper (⊤ : Subgroup ↥H)) = ⊤ := hmap.symm
    have hsup' : oTwoUpper (⊤ : Subgroup ↥H) ⊔ π.ker = ⊤ := by
      have h := Subgroup.comap_map_eq (f := π) (H := oTwoUpper (⊤ : Subgroup ↥H))
      rw [hKtop, Subgroup.comap_top] at h
      exact h.symm
    have hker : π.ker = CFSG.Open.pCore 2 ↥H := QuotientGroup.ker_mk' _
    have hmap2 : (oTwoUpper (⊤ : Subgroup ↥H) ⊔ CFSG.Open.pCore 2 ↥H).map H.subtype = H := by
      rw [hker] at hsup'
      rw [hsup', Subgroup.map_top, Subgroup.range_subtype]
    rw [Subgroup.map_sup, ← oTwoUpper_map H.subtype (⊤ : Subgroup ↥H), Subgroup.map_top,
      Subgroup.range_subtype] at hmap2
    have hp : Subgroup.map H.subtype (CFSG.Open.pCore 2 ↥H) = Q := by
      simpa [pCoreOf] using hpCore
    rw [hp] at hmap2
    exact hmap2
  have h1 : H ≤ oTwoUpper H ⊔ S := by
    calc H = oTwoUpper H ⊔ Q := hsupQ.symm
      _ ≤ oTwoUpper H ⊔ S := sup_le_sup_left hQS _
  have h2 : oTwoUpper H ⊔ S ≤ H := sup_le (oTwoUpper_le H) le_sup_right
  exact le_antisymm (le_trans h2 le_rfl) h1

theorem str86UN_noncentral {L1 L2 S : Subgroup G} {N : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hN : IsElemAbelian 2 N) (hNne : N ≠ ⊥)
    (hNZ : N ≤ Z1 L1 L2 S)
    (hNP1 : P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G))
    (hHT : oTwoUpper (L2 ⊔ S) ⊔ S = L2 ⊔ S)
    (hUe : IsPGroup 2 (str86UN N L2 S)) :
    ¬ IsChiefSeriesFrom (L2 ⊔ S) (str86UN N L2 S) (str86UN N L2 S) 0 := by
  intro hser
  have hzero : ⁅str86UN N L2 S, oTwoUpper (L2 ⊔ S)⁆ = ⊥ :=
    CFSG.Quasithin.D14.commutator_eq_bot_of_zero hUe hser rfl
  have hUC : str86UN N L2 S ≤ Subgroup.centralizer (oTwoUpper (L2 ⊔ S) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hzero
  have hO2C : oTwoUpper (L2 ⊔ S) ≤ Subgroup.centralizer (str86UN N L2 S : Set G) :=
    Subgroup.le_centralizer_iff.mp hUC
  have hNUN : N ≤ str86UN N L2 S := le_conjClosure N (L2 ⊔ S)
  have hO2N : oTwoUpper (L2 ⊔ S) ≤ Subgroup.normalizer (N : Set G) :=
    hO2C.trans ((Subgroup.centralizer_le hNUN).trans
      (Subgroup.centralizer_le_normalizer (N : Set G)))
  have hSN : S ≤ Subgroup.normalizer (N : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S)).trans
      ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans hNP1)
  have hGbeta : L2 ⊔ S ≤ Subgroup.normalizer (N : Set G) := by
    rw [← hHT]
    exact sup_le hO2N hSN
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (N : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans hNP1
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (N : Set G) :=
    sup_le (le_sup_left.trans hGbeta) hBN
  have hG0eq : P1 L1 L2 S ⊔ P2 L1 L2 S = L1 ⊔ L2 ⊔ S :=
    F1.parabolic_sup_parabolic L1 L2 S
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (N : Set G) := by
    rw [← hG0eq]
    exact sup_le hNP1 hP2N
  have hP1G0 : P1 L1 L2 S ≤ L1 ⊔ L2 ⊔ S := by
    rw [← hG0eq]
    exact le_sup_left
  have hQ1P1 : Q1 L1 L2 S ≤ P1 L1 L2 S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hNle : N ≤ L1 ⊔ L2 ⊔ S :=
    hNZ.trans ((A4.omegaOneCenterOf_le (Q1 L1 L2 S)).trans (hQ1P1.trans hP1G0))
  have hp := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNle hG0N hN.isPGroup
  rw [hF.1.o2] at hp
  exact hNne (le_bot_iff.mp hp)
