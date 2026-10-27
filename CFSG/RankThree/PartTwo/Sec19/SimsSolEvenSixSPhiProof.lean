module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSIso

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace SixPhiProof

theorem card_centralizer_even_involution {σ : Perm (Fin 6)} (h1 : σ ≠ 1) (h2 : σ * σ = 1)
    (hs : Perm.sign σ = 1) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 6)))) = 16 := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hord ▸ Nat.prime_two)
  rw [hord] at hn
  have hsum := Equiv.Perm.sum_cycleType_le σ
  have hsign := Equiv.Perm.sign_of_cycleType σ
  rw [hn, Multiset.sum_replicate, Multiset.card_replicate, hs] at hsign
  rw [hn, Multiset.sum_replicate, Fintype.card_fin] at hsum
  have hn1 : n = 1 := by
    have hle : n ≤ 2 := by simp at hsum; omega
    interval_cases n
    · exfalso
      revert hsign
      decide
    · rfl
    · exfalso
      revert hsign
      decide
  subst hn1
  rw [Equiv.Perm.nat_card_centralizer, hn]
  decide

end SixPhiProof

theorem SixPhiProof.barInd_singleton_notMem_range (a : Fin 6) :
    barInd ({a} : Finset (Fin 6)) ∉ Set.range (heartToBar (n := 6)) := by
  rintro ⟨u, hu⟩
  obtain ⟨e, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [heartToBar_mk] at hu
  have hu' : ((e : Fin 6 → ZMod 2) : permBar 6) =
      ((indVec ({a} : Finset (Fin 6)) : Fin 6 → ZMod 2) : permBar 6) := hu
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hu')
  have he : ∑ i, (e : Fin 6 → ZMod 2) i = 0 := by
    simpa [evenWeight, AddMonoidHom.mem_ker] using e.2
  have h1 : ∑ i, indVec ({a} : Finset (Fin 6)) i = 1 := by
    simp [indVec]
  have h2 : ∑ i, (k • allOnes 6) i = 0 := by
    have hc : ∀ i, (k • allOnes 6) i = (k : ZMod 2) := fun i => by
      simp [allOnes]
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    generalize (k : ZMod 2) = c
    revert c
    decide
  rw [hk] at h2
  simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib, he,
    h1, neg_zero, zero_add] at h2
  exact one_ne_zero h2

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

section Residual

variable (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ)
  (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) (hK : ¬ CGOf x ≤ M)
  (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x)
include hR2 hsurj hQ16 hij hπ hK h

theorem sixPhi_sq_eq_one : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1 := by
  classical
  have hR : Nat.card ↥(Rc X) ≤ 2 := hR2.le
  by_contra hall
  push Not at hall
  obtain ⟨q₀, hq₀, hq₀1⟩ := hall
  have hpar : ∀ (q : G) (hq : q ∈ CFSG.Open.pCoreOf 2 M), (q * q = 1 ↔
      Multiplicative.toAdd (D.piQ ⟨q, hq⟩) ∈ Set.range (heartToBar (n := 6))) := by
    rcases D.sq_eq_parity hR with h1 | h1
    · exact absurd (h1 q₀ hq₀) hq₀1
    · exact h1
  obtain ⟨r, hrR, hr1, t, htt, hθt, horb, hcomm⟩ :=
    D.sixInv_exists hR2 hsurj hQ16 hx hij hπ hK h
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    have h' := hrR
    rw [C.S.R_eq_inf] at h'
    exact h'.1
  obtain ⟨k, hkK, hkt⟩ := (horb t).2 (Or.inr (Or.inl rfl))
  have htr : (t : G) ≠ r := by
    intro he
    have hker : (⟨r, pCoreOf_le_self M hrQ⟩ : ↥M) ∈ C.θ.ker := by
      rw [C.theta_ker_eq hR]
      exact Subgroup.mem_subgroupOf.2 hrQ
    have h1 : C.θ t = 1 := by
      rw [show t = ⟨r, pCoreOf_le_self M hrQ⟩ from Subtype.ext he]
      exact hker
    rw [hθt] at h1
    have h2 := congrArg (fun σ : Perm (Fin 6) => σ i) h1
    simp only [swap_apply_left, Perm.one_apply] at h2
    exact hij h2.symm
  obtain ⟨a, haJ⟩ : ({i, j}ᶜ : Finset (Fin 6)).Nonempty :=
    Finset.card_pos.1 (by rw [SixS.card_compl_pair hij]; norm_num)
  have ha : a ∉ ({i, j} : Finset (Fin 6)) := Finset.mem_compl.1 haJ
  have hai : a ≠ i := fun he => ha (he ▸ Finset.mem_insert_self _ _)
  have haj : a ≠ j := fun he => ha (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hq₀π : Multiplicative.toAdd (D.piQ ⟨q₀, hq₀⟩) ∉ Set.range (heartToBar (n := 6)) :=
    fun hm => hq₀1 ((hpar q₀ hq₀).2 hm)
  obtain ⟨u, hu⟩ := add_mem_range_heartToBar (SixPhiProof.barInd_singleton_notMem_range a) hq₀π
  obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
  let wq : ↥(CFSG.Open.pCoreOf 2 M) := ⟨(w : G), C.S.W_le_Q w.2⟩
  have hwπ : Multiplicative.toAdd (D.piQ wq) =
      barInd ({a} : Finset (Fin 6)) + Multiplicative.toAdd (D.piQ ⟨q₀, hq₀⟩) := by
    rw [D.piQ_W w wq rfl, hw, toAdd_ofAdd, hu]
  have hyQ : q₀ * (w : G) ∈ CFSG.Open.pCoreOf 2 M := (CFSG.Open.pCoreOf 2 M).mul_mem hq₀ wq.2
  set y : G := q₀ * (w : G) with hydef
  have hyπ : Multiplicative.toAdd (D.piQ ⟨y, hyQ⟩) = barInd ({a} : Finset (Fin 6)) := by
    have e : (⟨y, hyQ⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = ⟨q₀, hq₀⟩ * wq := rfl
    rw [e, map_mul, toAdd_mul, hwπ, add_comm (barInd _), ← add_assoc, permBar_add_self,
      zero_add]
  have hyy1 : y * y ≠ 1 := fun h1 =>
    SixPhiProof.barInd_singleton_notMem_range a (hyπ ▸ (hpar y hyQ).1 h1)
  have hyyr : y * y = r := by
    have hne : (⟨y * y, D.sq_mem_R hyQ⟩ : ↥(Rc X)) ≠ 1 := fun he => hyy1 (congrArg Subtype.val he)
    have hne' : (⟨r, hrR⟩ : ↥(Rc X)) ≠ 1 := fun he => hr1 (congrArg Subtype.val he)
    exact congrArg Subtype.val (eq_of_card_le_two hR hne hne')
  have hxR : x ∉ Rc X := by
    intro hxR
    have h1 : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = 0 := by
      rw [(D.piQ_eq_one_iff ⟨x, hx⟩).2 hxR, toAdd_one]
    have h2 := SixS.barLen_barInd_pair hij
    rw [← hπ, h1, H4b.barLen_zero'] at h2
    norm_num at h2
  have hyt : y * t = t * y := by
    have hc : (t : G) * y * (t : G)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (CFSG.Open.pCoreOf 2 M).mul_mem (pCoreOf_normalized M t.2 hyQ)
        ((CFSG.Open.pCoreOf 2 M).inv_mem hyQ)
    have hcπ : Multiplicative.toAdd (D.piQ ⟨_, hc⟩) = 0 := by
      rw [SixSOne.toAdd_piQ_comm D t ⟨y, hyQ⟩ hc, hθt, hyπ, barAct_barInd, Finset.image_singleton,
        swap_apply_of_ne_of_ne hai haj, sub_self]
    have hcR : (t : G) * y * (t : G)⁻¹ * y⁻¹ ∈ Rc X := by
      refine (D.piQ_eq_one_iff ⟨_, hc⟩).1 ?_
      apply Multiplicative.toAdd.injective
      rw [hcπ, toAdd_one]
    have hcy := hcomm y hyQ
    simp only [InvMemClass.coe_inv] at hcy
    rcases hcy with h1 | h1
    · calc y * t = (y * t * y⁻¹ * (t : G)⁻¹) * (t * y) := by group
        _ = t * y := by rw [h1, one_mul]
    · exfalso
      have hxr : (x * r)⁻¹ ∈ Rc X := by
        rw [show (x * r)⁻¹ = (t : G) * y * (t : G)⁻¹ * y⁻¹ by rw [← h1]; group]
        exact hcR
      apply hxR
      have h2 : x = (x * r)⁻¹⁻¹ * r⁻¹ := by group
      rw [h2]
      exact (Rc X).mul_mem ((Rc X).inv_mem hxr) ((Rc X).inv_mem hrR)
  have htk : (t : G) = k * r * k⁻¹ := hkt
  have hr_eq : r = k⁻¹ * t * k := by rw [htk]; group
  have hy'M : k⁻¹ * y * k ∈ M := by
    refine C.S.centralizer_le_of_mem_R hrR hr1 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    calc k⁻¹ * y * k * r = k⁻¹ * (y * t) * k := by rw [hr_eq]; group
      _ = k⁻¹ * (t * y) * k := by rw [hyt]
      _ = r * (k⁻¹ * y * k) := by rw [hr_eq]; group
  have hr'eq : k⁻¹ * r * k = (k⁻¹ * y * k) * (k⁻¹ * y * k) := by
    rw [← hyyr]; group
  have hr'M : k⁻¹ * r * k ∈ M := hr'eq ▸ M.mul_mem hy'M hy'M
  have hr'Q : k⁻¹ * r * k ∉ CFSG.Open.pCoreOf 2 M := by
    intro hr'Q
    have hl0 : barLen (Multiplicative.toAdd (D.piQ ⟨r, hrQ⟩)) ≠ 2 := by
      rw [(D.piQ_eq_one_iff ⟨r, hrQ⟩).2 hrR, toAdd_one, H4b.barLen_zero']
      norm_num
    have hk' : k⁻¹ ∈ M :=
      D.mem_M_of_conj_len_ne_two hR hsurj hrQ hr1 hl0 (g := k⁻¹) (by simpa using hr'Q)
    have hkM : k ∈ M := by simpa using M.inv_mem hk'
    exact htr (by rw [htk]; exact C.R_central hR k hkM r hrR)
  set σ : Perm (Fin 6) := C.θ ⟨k⁻¹ * r * k, hr'M⟩ with hσdef
  have hσsq : σ = C.θ ⟨k⁻¹ * y * k, hy'M⟩ * C.θ ⟨k⁻¹ * y * k, hy'M⟩ := by
    rw [← map_mul]
    exact congrArg C.θ (Subtype.ext hr'eq)
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    have e : (⟨k⁻¹ * r * k, hr'M⟩ : ↥M) * ⟨k⁻¹ * r * k, hr'M⟩ = 1 := by
      apply Subtype.ext
      show k⁻¹ * r * k * (k⁻¹ * r * k) = 1
      have hrr := Rc_mul_self hR hrR
      calc k⁻¹ * r * k * (k⁻¹ * r * k) = k⁻¹ * (r * r) * k := by group
        _ = 1 := by rw [hrr]; group
    rw [e, map_one]
  have hσ1 : σ ≠ 1 := fun h1 => hr'Q (SixTwoAux.mem_Q_of_theta_eq_one C hR hr'M h1)
  have hσs : Perm.sign σ = 1 := by
    rw [hσsq, map_mul]
    exact Int.units_mul_self _
  have hC16 := SixPhiProof.card_centralizer_even_involution hσ1 hσ2 hσs
  have hcard := C.card_eq_card_inf_mul hR (inf_le_left : CMOf M (k⁻¹ * r * k) ≤ M)
  have himg : ((CMOf M (k⁻¹ * r * k)).subgroupOf M).map C.θ ≤
      Subgroup.centralizer ({σ} : Set (Perm (Fin 6))) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hm' : (m : G) ∈ CMOf M (k⁻¹ * r * k) := Subgroup.mem_subgroupOf.1 hm
    have hmr : (m : G) * (k⁻¹ * r * k) * (m : G)⁻¹ = k⁻¹ * r * k :=
      mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hm').2
    have e : m * ⟨k⁻¹ * r * k, hr'M⟩ = ⟨k⁻¹ * r * k, hr'M⟩ * m := by
      apply Subtype.ext
      show (m : G) * (k⁻¹ * r * k) = k⁻¹ * r * k * m
      calc (m : G) * (k⁻¹ * r * k) = ((m : G) * (k⁻¹ * r * k) * (m : G)⁻¹) * m := by group
        _ = k⁻¹ * r * k * m := by rw [hmr]
    rw [hσdef, ← map_mul, ← map_mul, e]
  have himg_card : Nat.card ↥(((CMOf M (k⁻¹ * r * k)).subgroupOf M).map C.θ) ≤ 16 :=
    hC16 ▸ Subgroup.card_le_of_le himg
  have hHQ : CMOf M (k⁻¹ * r * k) ⊓ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 M := inf_le_right
  have hHne : CMOf M (k⁻¹ * r * k) ⊓ CFSG.Open.pCoreOf 2 M ≠ CFSG.Open.pCoreOf 2 M := by
    intro he
    apply hr'Q
    rw [← C.centralizer_Q_eq hR, Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ CMOf M (k⁻¹ * r * k) ⊓ CFSG.Open.pCoreOf 2 M := by
      rw [he]
      exact hq
    have hqr : q * (k⁻¹ * r * k) * q⁻¹ = k⁻¹ * r * k :=
      mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hq').1).2
    calc q * (k⁻¹ * r * k) = (q * (k⁻¹ * r * k) * q⁻¹) * q := by group
      _ = k⁻¹ * r * k * q := by rw [hqr]
  have h2H : 2 * Nat.card ↥(CMOf M (k⁻¹ * r * k) ⊓ CFSG.Open.pCoreOf 2 M) ≤
      Nat.card ↥(CFSG.Open.pCoreOf 2 M) := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHQ
    have hpos : 0 < Nat.card ↥(CMOf M (k⁻¹ * r * k) ⊓ CFSG.Open.pCoreOf 2 M) := Nat.card_pos
    have hQpos : 0 < Nat.card ↥(CFSG.Open.pCoreOf 2 M) := Nat.card_pos
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hHne (Subgroup.eq_of_le_of_card_ge hHQ (by rw [hm, mul_one]))
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      omega
    rw [hm]
    have : 2 ≤ m := by omega
    nlinarith
  have hCt : Nat.card ↥(CMOf M t) ≤ Nat.card ↥(CMOf M (k⁻¹ * r * k)) := by
    refine Nat.card_le_card_of_injective
      (fun c => ⟨k⁻¹ * (c : G) * k, ?_⟩) ?_
    · obtain ⟨hcM, hcc⟩ := Subgroup.mem_inf.1 c.2
      have hct : (c : G) * t * (c : G)⁻¹ = t := mem_centralizer_zpowers_iff.1 hcc
      have hcr : (c : G) * r * (c : G)⁻¹ = r := C.R_central hR c hcM r hrR
      refine Subgroup.mem_inf.2 ⟨?_, mem_centralizer_zpowers_iff.2 ?_⟩
      · refine C.S.centralizer_le_of_mem_R hrR hr1
          (Subgroup.mem_centralizer_singleton_iff.2 ?_)
        calc k⁻¹ * (c : G) * k * r = k⁻¹ * ((c : G) * t * (c : G)⁻¹) * (c : G) * k := by
              rw [hr_eq]; group
          _ = r * (k⁻¹ * (c : G) * k) := by rw [hct, hr_eq]; group
      · calc k⁻¹ * (c : G) * k * (k⁻¹ * r * k) * (k⁻¹ * (c : G) * k)⁻¹ =
              k⁻¹ * ((c : G) * r * (c : G)⁻¹) * k := by group
          _ = k⁻¹ * r * k := by rw [hcr]
    · intro c c' he
      apply Subtype.ext
      have h1 := congrArg Subtype.val he
      simpa using h1
  have htri : ∀ c ∈ CMOf M x, c * t * c⁻¹ = t ∨ c * t * c⁻¹ = t * (x * r) := by
    intro c hc
    obtain ⟨hcM, hcx⟩ := Subgroup.mem_inf.1 hc
    have hcr : c * r * c⁻¹ = r := C.R_central hR c hcM r hrR
    have hmem : ∃ k' ∈ CGOf x, c * t * c⁻¹ = k' * r * k'⁻¹ :=
      ⟨c * k, (CGOf x).mul_mem hcx hkK, by rw [htk]; group⟩
    rcases (horb _).1 hmem with h1 | h1 | h1
    · exfalso
      apply htr
      have hcr' : c⁻¹ * r * c⁻¹⁻¹ = r := C.R_central hR c⁻¹ (M.inv_mem hcM) r hrR
      calc (t : G) = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = r := by rw [h1]; simpa using hcr'
    · exact Or.inl h1
    · exact Or.inr h1
  have hxt : Nat.card ↥(CMOf M x) ≤ 2 * Nat.card ↥(CMOf M t) := by
    by_cases hc₀ : ∃ c₀ ∈ CMOf M x, c₀ * t * c₀⁻¹ ≠ t
    · obtain ⟨c₀, hc₀M, hc₀t⟩ := hc₀
      have hc₀eq : c₀ * t * c₀⁻¹ = t * (x * r) := (htri c₀ hc₀M).resolve_left hc₀t
      have hc₀M' : c₀ ∈ M := (Subgroup.mem_inf.1 hc₀M).1
      have hinj : Nat.card ↥(CMOf M x) ≤ Nat.card (↥(CMOf M t) ⊕ ↥(CMOf M t)) := by
        refine Nat.card_le_card_of_injective (fun c => if hct : (c : G) * t * (c : G)⁻¹ = t then
          Sum.inl ⟨c, Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 c.2).1,
            mem_centralizer_zpowers_iff.2 hct⟩⟩ else
          Sum.inr ⟨c₀⁻¹ * c, Subgroup.mem_inf.2 ⟨M.mul_mem (M.inv_mem hc₀M')
            (Subgroup.mem_inf.1 c.2).1, mem_centralizer_zpowers_iff.2 ?_⟩⟩) ?_
        · have h1 := (htri c c.2).resolve_left hct
          calc c₀⁻¹ * (c : G) * t * (c₀⁻¹ * (c : G))⁻¹ = c₀⁻¹ * ((c : G) * t * (c : G)⁻¹) * c₀ := by
                group
            _ = c₀⁻¹ * (c₀ * t * c₀⁻¹) * c₀ := by rw [h1, hc₀eq]
            _ = t := by group
        · intro c c' he
          by_cases h1 : (c : G) * t * (c : G)⁻¹ = t <;>
            by_cases h2 : (c' : G) * t * (c' : G)⁻¹ = t <;>
            simp only [h1, h2, dite_true, dite_false, reduceCtorEq, Sum.inl.injEq,
              Sum.inr.injEq, Subtype.mk.injEq] at he
          · exact Subtype.ext he
          · exact Subtype.ext (mul_left_cancel he)
      rw [Nat.card_sum] at hinj
      omega
    · push Not at hc₀
      have hle : CMOf M x ≤ CMOf M t := fun c hc =>
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hc).1, mem_centralizer_zpowers_iff.2 (hc₀ c hc)⟩
      have := Subgroup.card_le_of_le hle
      omega
  have h15 := D.card_M_eq_fifteen hR hx (by rw [hπ]; exact SixS.barLen_barInd_pair hij)
  have hMcard : Nat.card ↥M = Nat.card ↥(CFSG.Open.pCoreOf 2 M) * 720 := by
    have h1 := C.card_eq_card_inf_mul hR (le_refl M)
    rw [inf_eq_right.2 (pCoreOf_le_self M)] at h1
    rw [h1, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hsurj,
      Subgroup.card_top, Nat.card_perm]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hQpos : 0 < Nat.card ↥(CFSG.Open.pCoreOf 2 M) := Nat.card_pos
  have hbound : Nat.card ↥(CMOf M (k⁻¹ * r * k)) ≤
      Nat.card ↥(CMOf M (k⁻¹ * r * k) ⊓ CFSG.Open.pCoreOf 2 M) * 16 := by
    rw [hcard]
    exact Nat.mul_le_mul_left _ himg_card
  omega

end Residual

end Cfg.PiData

theorem sixSymPhiQ_holds : SixSymPhiQ :=
  fun _ _ _ _ _ _ D hR2 hsurj _ hx _ _ hij hπ hK h =>
    D.sixPhi_sq_eq_one hR2 hsurj (D.card_Q_ne_sixteen_of_card_Rc hR2) hx hij hπ hK h

theorem sixSymResidual_holds : SixSymResidual :=
  sixSymResidual_of_phiQ sixSymPhiQ_holds sixSymResidualElem_holds

end CFSG.RankThree.PartTwo.Sec19.SolEven
