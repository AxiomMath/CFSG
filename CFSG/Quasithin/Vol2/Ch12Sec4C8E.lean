module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Set
public import CFSG.Quasithin.Background.E6Nineteen

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique S1248

@[expose] def A7Insp1248 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y) (z u : Y),
    CFSG.IsQuasisimple ↥K → E6.IsA7Type K → IsSylowTwoOf S K →
    z ∈ Subgroup.normalizer (K : Set Y) → z ∈ Subgroup.centralizer (S : Set Y) → z ^ 2 = 1 →
    u ∈ Subgroup.normalizer (K : Set Y) → u ∈ Subgroup.centralizer (S : Set Y) → u ^ 2 = 1 →
    u ∉ Subgroup.centralizer (K : Set Y) → u * z ∉ Subgroup.centralizer (K : Set Y) →
    ∃ k ∈ K, k * z = z * k ∧ k * u ≠ u * k

namespace S1248

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_centralizer_of_mul_mem {K D : Subgroup G} {z u : G}
    (huz : u * z ∈ Subgroup.centralizer (K : Set G)) (huK : u ∈ Subgroup.normalizer (K : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hDu : D ≤ Subgroup.centralizer ({u} : Set G))
    (hinv : ∀ d ∈ D, z⁻¹ * d * z = d⁻¹) (hord : ∀ d ∈ D, Odd (orderOf d)) (hu2 : u ^ 2 = 1)
    (hz2 : z ^ 2 = 1) : D ≤ Subgroup.centralizer (K : Set G) := by
  have hzinv : z⁻¹ = z := by rw [inv_eq_iff_mul_eq_one, ← sq, hz2]
  have hzu : ∀ k ∈ K, z⁻¹ * k * z = u * k * u⁻¹ := by
    intro k hk
    have hk' : u * k * u⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 huK k).1 hk
    have hc : u * k * u⁻¹ * (u * z) = u * z * (u * k * u⁻¹) :=
      Subgroup.mem_centralizer_iff.1 huz _ hk'
    calc z⁻¹ * k * z = (u * z)⁻¹ * ((u * k * u⁻¹) * (u * z)) := by group
      _ = (u * z)⁻¹ * ((u * z) * (u * k * u⁻¹)) := by rw [hc]
      _ = u * k * u⁻¹ := by group
  intro d hd
  have hdu : d * u = u * d := Subgroup.mem_centralizer_singleton_iff.1 (hDu hd)
  have hdK := hDK hd
  have e1 : z⁻¹ * d * z = d⁻¹ := hinv d hd
  have e2 : z⁻¹ * d⁻¹ * z = d := by
    calc z⁻¹ * d⁻¹ * z = (z⁻¹ * d * z)⁻¹ := by group
      _ = d := by rw [e1, inv_inv]
  have key : ∀ k ∈ K, d⁻¹ * k * d = d * k * d⁻¹ := by
    intro k hk
    have hk1 : d * k * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hdK k).1 hk
    have hk2 : u * (d * k * d⁻¹) * u⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 huK _).1 hk1
    have hconj : d * (u * k * u⁻¹) * d⁻¹ = u * (d * k * d⁻¹) * u⁻¹ := by
      calc d * (u * k * u⁻¹) * d⁻¹ = (d * u) * k * (d * u)⁻¹ := by group
        _ = (u * d) * k * (u * d)⁻¹ := by rw [hdu]
        _ = u * (d * k * d⁻¹) * u⁻¹ := by group
    calc d⁻¹ * k * d = (z⁻¹ * d * z) * k * (z⁻¹ * d⁻¹ * z) := by rw [e1, e2]
      _ = z⁻¹ * (d * (z * k * z⁻¹) * d⁻¹) * z := by group
      _ = z⁻¹ * (d * (z⁻¹ * k * z) * d⁻¹) * z := by rw [hzinv]
      _ = z⁻¹ * (u * (d * k * d⁻¹) * u⁻¹) * z := by rw [hzu k hk, hconj]
      _ = u * (u * (d * k * d⁻¹) * u⁻¹) * u⁻¹ := hzu _ hk2
      _ = (u * u) * (d * k * d⁻¹) * (u * u)⁻¹ := by group
      _ = d * k * d⁻¹ := by rw [← sq, hu2]; group
  have hd2 : d ^ 2 ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [sq]
    calc k * (d * d) = d * (d⁻¹ * k * d) * d⁻¹ * (d * d) := by group
      _ = d * (d * k * d⁻¹) * d⁻¹ * (d * d) := by rw [key k hk]
      _ = d * d * k := by group
  obtain ⟨j, hj⟩ := E6.pow_sq_eq_self (hord d hd)
  rw [← hj]
  exact Subgroup.pow_mem _ hd2 j

end S1248

theorem oddCentE1248_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hpre : Pre1242) (hinv : InvolFact1248)
    (hlist : Lemma115_3_List) (hP3 : E6.E619Insp) (hA7 : A7Insp1248) : OddCentE1248 := by
  intro G _ _ T L V U hS U₀ hU₀U hidx K hK
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hF⟩ := S1248.exists_facts h331 h1222 h323 h3228 hpre hS
  have hyp := hS.cx.hyp
  have := hyp.simple
  set H := Subgroup.centralizer (U₀ : Set G) with hHdef
  set D := oddCoreIn (Subgroup.centralizer (U : Set G)) with hDdef
  have hW₀ : U₀ = U ∨ (U₀ ≤ U ∧ U₀.relIndex U = 2) := Or.inr ⟨hU₀U, hidx⟩
  have h115 := hF.lemma115Hyp hinv (Or.inl rfl)
  have h115₀ := hF.lemma115Hyp hinv hW₀
  have hinvD : ∀ d ∈ D, z⁻¹ * d * z = d⁻¹ := h115.inverts_oddCoreIn
  have hDodd : Odd (Nat.card D) := odd_card_oddCoreIn _
  have hDC : D ≤ Subgroup.centralizer (U : Set G) := oddCoreIn_le _
  have hDH : D ≤ H := hDC.trans (Subgroup.centralizer_le hU₀U)
  have hordD : ∀ d ∈ D, Odd (orderOf d) := fun d hd =>
    Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hd)
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQH : IsSylowTwoOf Q H := E6.e6_5_one hF.e61 (hF.mem_gamma hinv hW₀)
  have hVQ : V ≤ Q := hF.e61.le_inf_centralizer
  have hcenQ : ∀ v ∈ V, v ∈ Subgroup.centralizer (Q : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun q hq => (Subgroup.mem_centralizer_iff.1 hq.2 v hv).symm
  have hzV : z ∈ V := hF.z_mem
  have hKq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hzK : z ∈ Subgroup.normalizer (K : Set G) :=
    E6.mem_normalizer_of_mem_center_sylow hQH hK (hVQ hzV) (hcenQ z hzV)
  have hDK : D ≤ Subgroup.normalizer (K : Set G) := fun d hd =>
    E6.mem_normalizer_of_inverts hzK (E6.mem_normalizer_of_mem_center_sylow hQH
      (Unc25G2.isComponentIn_conjugate hK (hDH hd)) (hVQ hzV) (hcenQ z hzV))
      (hinvD d hd) (hordD d hd)
  obtain ⟨u, huU, huU₀⟩ : ∃ u ∈ U, u ∉ U₀ := by
    by_contra hall
    push Not at hall
    have h1 : U₀.relIndex U = 1 := Subgroup.relIndex_eq_one.2 fun x hx => hall x hx
    omega
  have huV : u ∈ V := hS.le huU
  have hCU := E6.centralizer_eq_inf_of_relIndex_two hU₀U hidx huU huU₀
  by_cases huK : u ∈ Subgroup.centralizer (K : Set G)
  ·
    have hKC : K ≤ Subgroup.centralizer (U : Set G) := by
      rw [hCU]
      exact le_inf hK.1 fun k hk => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 huK k hk)
    have hc := E6.commutator_eq_bot_of_odd hKq hDodd hDK (hKC.trans (le_normalizer_oddCoreIn _))
    exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc)
  ·
    by_contra hDK'
    set R := Q ⊓ Subgroup.normalizer (K : Set G) with hRdef
    have hRK : R ⊓ K = Q ⊓ K := by
      rw [hRdef, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : K ≤ _)]
    have hSK : IsSylowTwoOf (Q ⊓ K) K := E6.isSylowTwoOf_inf_of_subnormal' hQH hK.1 hK.2.2
    have hcases := (Lemma115_3_List.component_cases hlist hyp.simple hyp.nonabelian
      (qtkeCore_of_cat hyp.nonabelian hyp.qtke) h115₀ hK).2.2.2
    have huN : u ∈ Subgroup.normalizer (K : Set G) :=
      E6.mem_normalizer_of_mem_center_sylow hQH hK (hVQ huV) (hcenQ u huV)
    have hcenR : ∀ v ∈ V, v ∈ Subgroup.centralizer (R : Set G) := fun v hv =>
      Subgroup.centralizer_le (inf_le_left : R ≤ Q) (hcenQ v hv)
    have hDu : D ≤ Subgroup.centralizer ({u} : Set G) := fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hDC hd) u huU).symm
    have hQ2 : IsPGroup 2 Q := hyp.sylow.1.to_le inf_le_left
    have hz2 : z ^ 2 = 1 := hF.z_sq
    have hu2 : u ^ 2 = 1 := hF.cx.sq u huV
    have hIsA7 := hP3 G K R D z u hKq hcases (hQ2.to_le inf_le_left) inf_le_right
      (by rw [hRK]; exact hSK) ⟨hVQ hzV, hzK⟩ (hcenR z hzV) hz2
      ⟨hVQ huV, huN⟩ (hcenR u huV) hu2 huK hDodd hDK hDu hinvD hDK'
    have huz : u * z ∉ Subgroup.centralizer (K : Set G) := fun huz =>
      hDK' (S1248.le_centralizer_of_mul_mem huz huN hDK hDu hinvD hordD hu2 hz2)
    obtain ⟨k, hkK, hkz, hku⟩ := hA7 G K (Q ⊓ K) z u hKq hIsA7 hSK hzK
      (Subgroup.centralizer_le inf_le_left (hcenQ z hzV)) hz2 huN
      (Subgroup.centralizer_le inf_le_left (hcenQ u huV)) hu2 huK huz
    apply hku
    have hkM : k ∈ Subgroup.normalizer (L : Set G) := by
      rw [← hF.centralizer_z_eq]
      exact Subgroup.mem_centralizer_singleton_iff.2 hkz
    have hkV : k ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
      rw [← hF.inf_centralizer_eq hinv hW₀]
      exact ⟨hkM, hK.1 hkK⟩
    exact (Subgroup.mem_centralizer_iff.1 hkV.2 u huV).symm

end CFSG.Quasithin.H13
