module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixLen2
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTI
import CFSG.RankThree.PartTwo.Sec15.Item1424Proof

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace Six

theorem barLen_le_three (v : permBar 6) : barLen v ≤ 3 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [barLen_mk]
  omega

theorem conj_mem_pCoreOf_of_normalizes {G : Type} [Group G] {H : Subgroup G} {k : G}
    (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) {o : G}
    (ho : o ∈ CFSG.Open.pCoreOf 2 H) : k * o * k⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
  set O : Subgroup G := (CFSG.Open.pCoreOf 2 H).map (MulAut.conj k).toMonoidHom with hO
  have hOH : O ≤ H := by
    rintro _ ⟨o', ho', rfl⟩
    exact hk o' (pCoreOf_le_self H ho')
  have hOn : ∀ h ∈ H, ∀ u ∈ O, h * u * h⁻¹ ∈ O := by
    rintro h hh _ ⟨o', ho', rfl⟩
    refine ⟨(k⁻¹ * h * k) * o' * (k⁻¹ * h * k)⁻¹, pCoreOf_normalized H (hk' h hh) ho', ?_⟩
    show k * ((k⁻¹ * h * k) * o' * (k⁻¹ * h * k)⁻¹) * k⁻¹ = h * (k * o' * k⁻¹) * h⁻¹
    group
  have hO2 : IsPGroup 2 O := (isPGroup_pCoreOf' H).map _
  exact le_pCoreOf_of_normalized hOH hOn hO2 ⟨o, ho, rfl⟩

end Six

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem exists_not_comm_of_fourGroup {J : Finset (Fin 6)} (hJ : J.card = 4)
    {F : Subgroup (Perm (Fin 6))} (hF : FourGroup J F) {N : Subgroup G}
    (hQN : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ u ∈ N, q * u * q⁻¹ ∈ N) {p p' : ↥M}
    (hp : (p : G) ∈ N) (hp' : (p' : G) ∈ N) (hσ : C.θ p ∈ F) (hσ1 : C.θ p ≠ 1)
    (hτ : C.θ p' ∈ F) (hτ1 : C.θ p' ≠ 1) (hne : C.θ p ≠ C.θ p') :
    ∃ d ∈ N, (p : G) * d ≠ d * p := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQdef
  obtain ⟨a, haJ⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := J) (t := (Finset.univ : Finset (Fin 6))) (by rw [hJ]; simp)
  obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd (pairEW a c : altHeart 6))
  have hwQ : (w : G) ∈ Q := C.S.W_le_Q w.2
  have hcw : (p' : G) * w * (p' : G)⁻¹ ∈ Q := pCoreOf_normalized M p'.2 hwQ
  set d : G := (p' : G) * w * (p' : G)⁻¹ * (w : G)⁻¹ with hd
  have hdN : d ∈ N := by
    have e : d = (p' : G) * ((w : G) * (p' : G)⁻¹ * (w : G)⁻¹) := by rw [hd]; group
    rw [e]
    exact N.mul_mem hp' (hQN _ hwQ _ (N.inv_mem hp'))
  have hdQ : d ∈ Q := Q.mul_mem hcw (Q.inv_mem hwQ)
  have hπw : Multiplicative.toAdd (D.piQ ⟨(w : G), hwQ⟩) = uvec a c := by
    rw [D.piQ_W w ⟨(w : G), hwQ⟩ rfl, hw]
    exact heartToBar_pairEW_eq_uvec a c
  have hτc : C.θ p' c = c := hF.fix _ hτ c hc
  have hπcw : Multiplicative.toAdd (D.piQ ⟨_, hcw⟩) = uvec (C.θ p' a) c := by
    rw [D.piQ_conj p' ⟨(w : G), hwQ⟩ ⟨_, hcw⟩ rfl, hπw, barAct_uvec, hτc]
  have hπd : Multiplicative.toAdd (D.piQ ⟨d, hdQ⟩) = uvec a (C.θ p' a) := by
    have e : (⟨d, hdQ⟩ : ↥Q) = ⟨_, hcw⟩ * (⟨(w : G), hwQ⟩ : ↥Q)⁻¹ := rfl
    rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, hπcw, hπw, add_comm]
    exact neg_uvec_add_uvec a (C.θ p' a) c
  refine ⟨d, hdN, fun hcomm => ?_⟩
  have hpd : (p : G) * d * (p : G)⁻¹ = d := by rw [hcomm]; group
  have h1 := D.piQ_conj p ⟨d, hdQ⟩ ⟨d, hdQ⟩ hpd.symm
  rw [hπd] at h1
  exact Six.FourGroup_barAct_uvec_ne hF hJ hσ hσ1 hτ hτ1 hne haJ h1.symm

theorem ne_one_of_len_two {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)}
    (hI : I.card = 2) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) : x ≠ 1 := by
  intro h1
  have h0 : barInd I = 0 := by
    rw [← hπ]
    have : (⟨x, hx⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 := Subtype.ext h1
    rw [this, map_one]
    rfl
  have h2 := barLen_barInd I
  rw [h0, ← barInd_empty, barLen_barInd, hI] at h2
  simp at h2

theorem pCore_facts_of_not_le (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I)
    (hK : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) ≤ TOf M x ∧
      ¬ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) ∧
      ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set G))).subgroupOf M).map C.θ =
        klein4 Iᶜ := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQdef
  set K : Subgroup G := Subgroup.centralizer ({x} : Set G) with hKdef
  set P : Subgroup G := CFSG.Open.pCoreOf 2 K with hPdef
  have hQab := C.Q_comm hR
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  have hKz : K = Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    centralizer_singleton_eq_zpowers x
  have hQK : Q ≤ K := fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hQab q hq x hx)
  have hPn : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P := fun k hk p hp => pCoreOf_normalized K hk hp
  have hQnP : Q ≤ Subgroup.normalizer (P : Set G) := fun q hq => by
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hPn q (hQK hq) p hp, fun hp => ?_⟩
    have := hPn q⁻¹ (K.inv_mem (hQK hq)) _ hp
    simpa [mul_assoc] using this
  set H : Subgroup G := P ⊔ Q with hHdef
  have hH2 : IsPGroup 2 H :=
    (isPGroup_pCoreOf' K).to_sup_of_normal_left' (isPGroup_pCoreOf' M) hQnP
  have hHK : H ≤ K := sup_le (pCoreOf_le_self K) hQK
  set N₀ : Subgroup G := H ⊓ M with hN₀
  have hconjH : ∀ k ∈ M, k ∈ K → ∀ h ∈ H, k * h * k⁻¹ ∈ H := by
    intro k hkM hkK h hh
    have hmap : H.map (MulAut.conj k).toMonoidHom ≤ H := by
      rw [hHdef, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨p, hp, rfl⟩
        exact hPn k hkK p hp
      · rintro _ ⟨q, hq, rfl⟩
        exact pCoreOf_normalized M hkM hq
    exact hmap ⟨h, hh, rfl⟩
  have hN₀T : N₀ ≤ TOf M x := by
    refine le_pCoreOf_of_normalized (fun u hu => ?_) (fun k hk u hu => ?_)
      (hH2.to_le inf_le_left)
    · obtain ⟨huH, huM⟩ := Subgroup.mem_inf.1 hu
      have huK : u ∈ K := hHK huH
      rw [hKz] at huK
      exact Subgroup.mem_inf.2 ⟨huM, huK⟩
    · obtain ⟨hkM, hkC⟩ := Subgroup.mem_inf.1 hk
      have hkK : k ∈ K := by rw [hKz]; exact hkC
      obtain ⟨huH, huM⟩ := Subgroup.mem_inf.1 hu
      exact Subgroup.mem_inf.2 ⟨hconjH k hkM hkK u huH,
        M.mul_mem (M.mul_mem hkM huM) (M.inv_mem hkM)⟩
  have hHN : H ≤ N₀ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥H := hH2.isNilpotent
    have hself : Subgroup.normalizer ((N₀.subgroupOf H : Subgroup ↥H) : Set ↥H) =
        N₀.subgroupOf H := by
      refine le_antisymm (fun h hh => ?_) Subgroup.le_normalizer
      have hconj : conjSubgroup (h : G) Q ≤ TOf M x := by
        rintro _ ⟨q, hq, rfl⟩
        have hqN : (⟨q, le_sup_right (a := P) hq⟩ : ↥H) ∈ N₀.subgroupOf H :=
          Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨le_sup_right (a := P) hq,
            pCoreOf_le_self M hq⟩)
        have := (Subgroup.mem_normalizer_iff.1 hh _).1 hqN
        exact hN₀T (Subgroup.mem_subgroupOf.1 this)
      have hEq := D.conj_eq_of_le_TOf_len_two hR halt hx hI hπ hconj
      have hhM : (h : G) ∈ M := by
        rw [← C.S.normalizer_Q_eq]
        exact TI.mem_normalizer_iff_conj.2 hEq
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨h.2, hhM⟩)
    have htop := (normalizerCondition_iff_only_full_group_self_normalizing.1
      (normalizerCondition_of_isNilpotent (G := ↥H))) _ hself
    intro h hh
    have : (⟨h, hh⟩ : ↥H) ∈ N₀.subgroupOf H := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hPT : P ≤ TOf M x := fun p hp => hN₀T (hHN (le_sup_left (b := Q) hp))
  have hPM : P ≤ M := hPT.trans (TOf_le_M M x)
  have hQP : ¬ Q ≤ P := by
    intro hQP
    apply hK
    intro k hk
    have hconj : conjSubgroup k Q ≤ TOf M x := by
      rintro _ ⟨q, hq, rfl⟩
      exact hPT (hPn k hk q (hQP hq))
    have hEq := D.conj_eq_of_le_TOf_len_two hR halt hx hI hπ hconj
    rw [← C.S.normalizer_Q_eq]
    exact TI.mem_normalizer_iff_conj.2 hEq
  refine ⟨hPT, hQP, ?_⟩
  have hx1 : x ≠ 1 := D.ne_one_of_len_two hx hI hπ
  have hcent := CFSG.RankThree.PartTwo.Sec15.inf_centralizer_le_pCoreOf_of_fitting
    (C.S.cent x hx hx1)
  have hθP_ne : (P.subgroupOf M).map C.θ ≠ ⊥ := by
    intro hbot
    apply hQP
    have hPQ : P ≤ Q := by
      intro p hp
      have h1 : C.θ ⟨p, hPM hp⟩ = 1 := by
        have : C.θ ⟨p, hPM hp⟩ ∈ (P.subgroupOf M).map C.θ := ⟨⟨p, hPM hp⟩, hp, rfl⟩
        rw [hbot] at this
        exact this
      rw [hQdef, ← C.K_eq_Q hR]
      exact C.mem_K.2 ⟨hPM hp, h1⟩
    intro q hq
    exact hcent (Subgroup.mem_inf.2 ⟨hQK hq,
      Subgroup.mem_centralizer_iff.2 fun p hp => (hQab q hq p (hPQ hp)).symm⟩)
  have hθPle : (P.subgroupOf M).map C.θ ≤ klein4 Iᶜ := by
    rw [← D.theta_TOf_len_two hR halt hx hI hπ]
    exact Subgroup.map_mono (fun m hm => hPT hm)
  have hθPn : ∀ τ ∈ altOn Iᶜ, ∀ σ ∈ (P.subgroupOf M).map C.θ,
      τ * σ * τ⁻¹ ∈ (P.subgroupOf M).map C.θ := by
    intro τ hτ σ hσ
    obtain ⟨c, hcC, hcθ⟩ :=
      Subgroup.mem_map.1 (D.altOn_le_theta_CMOf_six hx (by omega) hπ (Or.inr rfl) hτ)
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hσ
    have hcK : (c : G) ∈ K := by
      have := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hcC)).2
      rw [hKz]
      exact this
    have hcp : (c : G) * (p : G) * (c : G)⁻¹ ∈ P := hPn _ hcK _ (Subgroup.mem_subgroupOf.1 hp)
    refine Subgroup.mem_map.2 ⟨c * p * c⁻¹, Subgroup.mem_subgroupOf.2 hcp, ?_⟩
    rw [map_mul, map_mul, map_inv, hcθ]
  exact FourGroup.eq_of_le (klein4_fourGroup hIc) hIc hθPle hθP_ne hθPn

theorem klein4_ne_bot {J : Finset (Fin 6)} (hJ : J.card = 4) : klein4 J ≠ ⊥ := by
  intro h
  have := card_klein4 hJ
  rw [h, Subgroup.card_bot] at this
  omega

theorem exists_not_comm_pCore_len_two (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) {z : G}
    (hz : z ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨z, hz⟩) = barInd I) :
    ∃ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G)),
      ∃ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), a * b ≠ b * a := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQdef
  set K : Subgroup G := Subgroup.centralizer ({z} : Set G) with hKdef
  set P : Subgroup G := CFSG.Open.pCoreOf 2 K with hPdef
  have hQab := C.Q_comm hR
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  have hKz : K = Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    centralizer_singleton_eq_zpowers z
  have hQK : Q ≤ K := fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hQab q hq z hz)
  have hPn : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P := fun k hk p hp => pCoreOf_normalized K hk hp
  have hPM_θ : P ≤ M ∧ (P.subgroupOf M).map C.θ = klein4 Iᶜ := by
    by_cases hKM : K ≤ M
    · have hPT : P = TOf M z := by
        have h1 : M ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) = K := by
          rw [← hKz]
          exact inf_eq_right.2 hKM
        show CFSG.Open.pCoreOf 2 K = CFSG.Open.pCoreOf 2 (M ⊓ _)
        rw [h1]
      refine ⟨hPT ▸ TOf_le_M M z, ?_⟩
      rw [hPT]
      exact D.theta_TOf_len_two hR halt hz hI hπ
    · obtain ⟨hPT, -, hθ⟩ := D.pCore_facts_of_not_le hR halt hz hI hπ hKM
      exact ⟨hPT.trans (TOf_le_M M z), hθ⟩
  obtain ⟨hPM, hθP⟩ := hPM_θ
  have hF := klein4_fourGroup hIc
  obtain ⟨σ, hσ, hσ1, -⟩ := hF.exists_ne hIc (klein4_ne_bot hIc) 1
  obtain ⟨τ, hτ, hτ1, hτσ⟩ := hF.exists_ne hIc (klein4_ne_bot hIc) σ
  have hσ' := hσ
  have hτ' := hτ
  rw [← hθP] at hσ' hτ'
  obtain ⟨p, hp, hpσ⟩ := Subgroup.mem_map.1 hσ'
  obtain ⟨p', hp', hp'τ⟩ := Subgroup.mem_map.1 hτ'
  obtain ⟨d, hdP, hd⟩ := D.exists_not_comm_of_fourGroup hIc hF
    (N := P) (fun q hq u hu => hPn q (hQK hq) u hu) (Subgroup.mem_subgroupOf.1 hp)
    (Subgroup.mem_subgroupOf.1 hp') (hpσ ▸ hσ) (hpσ ▸ hσ1) (hp'τ ▸ hτ) (hp'τ ▸ hτ1)
    (by rw [hpσ, hp'τ]; exact Ne.symm hτσ)
  exact ⟨p, Subgroup.mem_subgroupOf.1 hp, d, hdP, hd⟩

theorem centralizer_le_M_len_two (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6))
    (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  classical
  by_contra hK
  obtain ⟨hPT, hQP, hθP⟩ := D.pCore_facts_of_not_le hR halt hx hI hπ hK
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQdef
  set K : Subgroup G := Subgroup.centralizer ({x} : Set G) with hKdef
  set P : Subgroup G := CFSG.Open.pCoreOf 2 K with hPdef
  have hQab := C.Q_comm hR
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  have hQK : Q ≤ K := fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hQab q hq x hx)
  have hPn : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P := fun k hk p hp => pCoreOf_normalized K hk hp
  have hQnP : ∀ q ∈ Q, ∀ u ∈ P, q * u * q⁻¹ ∈ P := fun q hq u hu => hPn q (hQK hq) u hu
  have hPM : P ≤ M := hPT.trans (TOf_le_M M x)
  have hx1 : x ≠ 1 := D.ne_one_of_len_two hx hI hπ
  have hcent := CFSG.RankThree.PartTwo.Sec15.inf_centralizer_le_pCoreOf_of_fitting
    (C.S.cent x hx hx1)
  have hF := klein4_fourGroup hIc
  have hZQ : ∀ z ∈ P, (∀ p ∈ P, z * p = p * z) → z ∈ Q := by
    intro z hz hzc
    by_contra hzQ
    have hθz : C.θ ⟨z, hPM hz⟩ ≠ 1 := fun h =>
      hzQ (by rw [hQdef, ← C.K_eq_Q hR]; exact C.mem_K.2 ⟨hPM hz, h⟩)
    have hσ : C.θ ⟨z, hPM hz⟩ ∈ klein4 Iᶜ := by
      rw [← hθP]
      exact ⟨⟨z, hPM hz⟩, hz, rfl⟩
    obtain ⟨τ, hτ, hτ1, hτσ⟩ := hF.exists_ne hIc (klein4_ne_bot hIc) (C.θ ⟨z, hPM hz⟩)
    have hτ' := hτ
    rw [← hθP] at hτ'
    obtain ⟨p', hp', hp'τ⟩ := Subgroup.mem_map.1 hτ'
    obtain ⟨d, hdP, hd⟩ := D.exists_not_comm_of_fourGroup hIc hF (N := P) hQnP
      (p := ⟨z, hPM hz⟩) hz (Subgroup.mem_subgroupOf.1 hp') hσ hθz (hp'τ ▸ hτ)
      (hp'τ ▸ hτ1) (by rw [hp'τ]; exact Ne.symm hτσ)
    exact hd (hzc d hdP)
  have hRbot : Rc X = ⊥ := by
    by_contra hRne
    obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRne
    have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
    have hrQ : r ∈ Q := by
      have hr' := hr
      rw [C.S.R_eq_inf] at hr'
      exact (Subgroup.mem_inf.1 hr').1
    set E : Subgroup G := P ⊓ Subgroup.centralizer (P : Set G) with hE
    have hrC : r ∈ Subgroup.centralizer (P : Set G) := Subgroup.mem_centralizer_iff.2 fun p hp => by
      have h1 := C.S.R_central hR (hPM hp) hr
      calc p * r = (p * r * p⁻¹) * p := by group
        _ = r * p := by rw [h1]
    have hrE : r ∈ E := Subgroup.mem_inf.2 ⟨hcent (Subgroup.mem_inf.2 ⟨hQK hrQ, hrC⟩), hrC⟩
    have hEQ : E ≤ Q := fun e he => hZQ e (Subgroup.mem_inf.1 he).1 fun p hp =>
      ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 he).2) p hp).symm
    have hEn : ∀ k ∈ K, ∀ e ∈ E, k * e * k⁻¹ ∈ E := by
      intro k hk e he
      obtain ⟨heP, heC⟩ := Subgroup.mem_inf.1 he
      refine Subgroup.mem_inf.2 ⟨hPn k hk e heP, Subgroup.mem_centralizer_iff.2 fun p hp => ?_⟩
      have hp' : k⁻¹ * p * k ∈ P := by
        have := hPn k⁻¹ (K.inv_mem hk) p hp
        simpa using this
      have h1 := (Subgroup.mem_centralizer_iff.1 heC) _ hp'
      calc p * (k * e * k⁻¹) = k * ((k⁻¹ * p * k) * e) * k⁻¹ := by group
        _ = k * (e * (k⁻¹ * p * k)) * k⁻¹ := by rw [h1]
        _ = k * e * k⁻¹ * p := by group
    set L : Subgroup G := K ⊓ Subgroup.centralizer (E : Set G) with hL
    have hLM : L ≤ M := fun l hl => by
      have hlr : l ∈ Subgroup.centralizer ({r} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hl).2) r hrE).symm
      exact C.S.centralizer_le_of_mem_R hr hr1' hlr
    have hQL : Q ≤ L := fun q hq => Subgroup.mem_inf.2 ⟨hQK hq,
      Subgroup.mem_centralizer_iff.2 fun e he => (hQab q hq e (hEQ he)).symm⟩
    have hQO : Q ≤ CFSG.Open.pCoreOf 2 L :=
      le_pCoreOf_of_normalized hQL (fun l hl q hq => pCoreOf_normalized M (hLM hl) hq)
        (isPGroup_pCoreOf' M)
    have hKL : ∀ k ∈ K, ∀ l ∈ L, k * l * k⁻¹ ∈ L := by
      intro k hk l hl
      obtain ⟨hlK, hlC⟩ := Subgroup.mem_inf.1 hl
      refine Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem hk hlK) (K.inv_mem hk),
        Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
      have he' : k⁻¹ * e * k ∈ E := by
        have := hEn k⁻¹ (K.inv_mem hk) e he
        simpa using this
      have h1 := (Subgroup.mem_centralizer_iff.1 hlC) _ he'
      calc e * (k * l * k⁻¹) = k * ((k⁻¹ * e * k) * l) * k⁻¹ := by group
        _ = k * (l * (k⁻¹ * e * k)) * k⁻¹ := by rw [h1]
        _ = k * l * k⁻¹ * e := by group
    have hOP : CFSG.Open.pCoreOf 2 L ≤ P :=
      le_pCoreOf_of_normalized ((pCoreOf_le_self L).trans inf_le_left)
        (fun k hk o ho => Six.conj_mem_pCoreOf_of_normalizes (hKL k hk)
          (fun l hl => by simpa using hKL k⁻¹ (K.inv_mem hk) l hl) ho)
        (isPGroup_pCoreOf' L)
    exact hQP (hQO.trans hOP)
  have hcardQ : Nat.card ↥Q = Nat.card ↥((Q.subgroupOf Q).map D.piQ) := by
    have h := D.card_eq_card_inf_R_mul (le_refl Q)
    rw [hRbot, inf_bot_eq, Subgroup.card_bot, one_mul] at h
    exact h
  have hWQ : 2 ^ (6 - 2) ≤ Nat.card ↥Q :=
    C.S.card_blockU_ge.trans (Subgroup.card_le_of_le C.S.W_le_Q)
  have hdvd : Nat.card ↥((Q.subgroupOf Q).map D.piQ) ∣ 32 := by
    have h := Subgroup.card_subgroup_dvd_card ((Q.subgroupOf Q).map D.piQ)
    have h32 : Nat.card (Multiplicative (permBar 6)) = 32 := by
      rw [show Nat.card (Multiplicative (permBar 6)) = Nat.card (permBar 6) from rfl,
        Comb.card_permBar (by norm_num)]
      norm_num
    rwa [h32] at h
  have htop : (Q.subgroupOf Q).map D.piQ = ⊤ := by
    have h32 : Nat.card ↥((Q.subgroupOf Q).map D.piQ) = 32 := by
      have hle : Nat.card ↥((Q.subgroupOf Q).map D.piQ) ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
      have hge : 16 ≤ Nat.card ↥((Q.subgroupOf Q).map D.piQ) := by
        rw [← hcardQ]
        norm_num at hWQ
        exact hWQ
      have hne : Nat.card ↥((Q.subgroupOf Q).map D.piQ) ≠ 16 := by rw [← hcardQ]; exact hQ16
      interval_cases h : Nat.card ↥((Q.subgroupOf Q).map D.piQ) <;> simp_all
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [h32, show Nat.card (Multiplicative (permBar 6)) = Nat.card (permBar 6) from rfl,
      Comb.card_permBar (by norm_num)]
    norm_num
  obtain ⟨a, haI⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  have hymem : Multiplicative.ofAdd (barInd ({a} : Finset (Fin 6))) ∈
      (Q.subgroupOf Q).map D.piQ := htop ▸ Subgroup.mem_top _
  obtain ⟨y, -, hyπ⟩ := Subgroup.mem_map.1 hymem
  have hyπ' : Multiplicative.toAdd (D.piQ y) = barInd ({a} : Finset (Fin 6)) := by
    rw [hyπ]
    rfl
  have hlen_y : barLen (Multiplicative.toAdd (D.piQ y)) = 1 := by
    rw [hyπ', barLen_barInd]
    simp
  have hy1 : (y : G) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext h1
    rw [this, map_one] at hlen_y
    have h0 : barLen (Multiplicative.toAdd (1 : Multiplicative (permBar 6))) = 0 := by
      show barLen (0 : permBar 6) = 0
      rw [← barInd_empty, barLen_barInd]
      simp
    omega
  have hπinj : ∀ q q' : ↥Q, D.piQ q = D.piQ q' → q = q' := by
    intro q q' h
    have h1 : D.piQ (q * q'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rw [D.piQ_eq_one_iff, hRbot] at h1
    have h2 : (q : G) * (q' : G)⁻¹ = 1 := h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  have hyT : ∀ t ∈ TOf M x, t * (y : G) = (y : G) * t := by
    intro t ht
    have htM : t ∈ M := TOf_le_M M x ht
    have hθt : C.θ ⟨t, htM⟩ ∈ klein4 Iᶜ := by
      rw [← D.theta_TOf_len_two hR halt hx hI hπ]
      exact C.mem_thetaN.2 ⟨⟨t, htM⟩, ht, rfl⟩
    have hta : C.θ ⟨t, htM⟩ a = a :=
      (mem_altOn.1 (klein4_le_altOn hIc hθt)).1 a (by simpa using haI)
    have hc : t * (y : G) * t⁻¹ ∈ Q := pCoreOf_normalized M htM y.2
    have h1 := D.piQ_conj ⟨t, htM⟩ y ⟨_, hc⟩ rfl
    rw [hyπ', barAct_barInd, Finset.image_singleton, hta, ← hyπ'] at h1
    have h2 : (⟨_, hc⟩ : ↥Q) = y := hπinj _ _ (Multiplicative.toAdd.injective h1)
    have h3 : t * (y : G) * t⁻¹ = y := congrArg Subtype.val h2
    calc t * (y : G) = (t * (y : G) * t⁻¹) * t := by group
      _ = (y : G) * t := by rw [h3]
  have hyP : (y : G) ∈ P := hcent (Subgroup.mem_inf.2 ⟨hQK y.2,
    Subgroup.mem_centralizer_iff.2 fun p hp => hyT p (hPT hp)⟩)
  apply hK
  intro g hg
  set y' : G := g * (y : G) * g⁻¹ with hy'
  have hy'P : y' ∈ P := hPn g hg _ hyP
  have hy'c : ∀ p ∈ P, y' * p = p * y' := by
    intro p hp
    have hp' : g⁻¹ * p * g ∈ P := by
      have := hPn g⁻¹ (K.inv_mem hg) p hp
      simpa using this
    have h1 := hyT _ (hPT hp')
    calc y' * p = g * ((y : G) * (g⁻¹ * p * g)) * g⁻¹ := by rw [hy']; group
      _ = g * ((g⁻¹ * p * g) * (y : G)) * g⁻¹ := by rw [h1]
      _ = p * y' := by rw [hy']; group
  have hy'Q : y' ∈ Q := hZQ y' hy'P hy'c
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hy1
    have : (y : G) = g⁻¹ * y' * g := by rw [hy']; group
    rw [this, h]
    group
  by_cases hl2 : barLen (Multiplicative.toAdd (D.piQ ⟨y', hy'Q⟩)) = 2
  ·
    exfalso
    obtain ⟨I', hI'c, hI'⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨y', hy'Q⟩))
    rw [hl2] at hI'c
    obtain ⟨u, hu, v, hv, huv⟩ := D.exists_not_comm_pCore_len_two hR halt hy'Q hI'c hI'
    have hOy := (D.centralizer_le_of_len hR y hy1
      ⟨by rw [hlen_y]; norm_num, by rw [hlen_y]; norm_num⟩).2
    have hconj : ∀ o ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({y'} : Set G)),
        g⁻¹ * o * g ∈ Q := by
      intro o ho
      set O : Subgroup G := (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({y'} : Set G))).map
        (MulAut.conj g⁻¹).toMonoidHom with hO
      have hOC : O ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
        rintro _ ⟨o', ho', rfl⟩
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (pCoreOf_le_self _ ho')
        rw [Subgroup.mem_centralizer_singleton_iff]
        show g⁻¹ * o' * g⁻¹⁻¹ * (y : G) = (y : G) * (g⁻¹ * o' * g⁻¹⁻¹)
        have e1 : (y : G) = g⁻¹ * y' * g := by rw [hy']; group
        rw [e1]
        calc g⁻¹ * o' * g⁻¹⁻¹ * (g⁻¹ * y' * g) = g⁻¹ * (o' * y') * g := by group
          _ = g⁻¹ * (y' * o') * g := by rw [h1]
          _ = g⁻¹ * y' * g * (g⁻¹ * o' * g⁻¹⁻¹) := by group
      have hOn : ∀ c ∈ Subgroup.centralizer ({(y : G)} : Set G), ∀ u ∈ O, c * u * c⁻¹ ∈ O := by
        rintro c hc _ ⟨o', ho', rfl⟩
        have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer ({y'} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
          rw [hy']
          calc g * c * g⁻¹ * (g * (y : G) * g⁻¹) = g * (c * (y : G)) * g⁻¹ := by group
            _ = g * ((y : G) * c) * g⁻¹ := by rw [hc]
            _ = g * (y : G) * g⁻¹ * (g * c * g⁻¹) := by group
        refine ⟨(g * c * g⁻¹) * o' * (g * c * g⁻¹)⁻¹, pCoreOf_normalized _ hc' ho', ?_⟩
        show g⁻¹ * ((g * c * g⁻¹) * o' * (g * c * g⁻¹)⁻¹) * g⁻¹⁻¹ =
          c * (g⁻¹ * o' * g⁻¹⁻¹) * c⁻¹
        group
      have hO2 : IsPGroup 2 O := (isPGroup_pCoreOf' _).map _
      have hle : O ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({(y : G)} : Set G)) :=
        le_pCoreOf_of_normalized hOC hOn hO2
      rw [hOy] at hle
      have : g⁻¹ * o * g⁻¹⁻¹ ∈ O := ⟨o, ho, rfl⟩
      simpa using hle this
    apply huv
    have h1 := hQab _ (hconj u hu) _ (hconj v hv)
    calc u * v = g * ((g⁻¹ * u * g) * (g⁻¹ * v * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * v * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
      _ = v * u := by group
  ·
    have hl4 : barLen (Multiplicative.toAdd (D.piQ ⟨y', hy'Q⟩)) ≠ 4 := fun h => by
      have := Six.barLen_le_three (Multiplicative.toAdd (D.piQ ⟨y', hy'Q⟩))
      omega
    exact D.mem_of_conj_of_len hR (x := y) (y := ⟨y', hy'Q⟩) hy1 hy'1
      ⟨by rw [hlen_y]; norm_num, by rw [hlen_y]; norm_num⟩ ⟨hl2, hl4⟩ rfl

include D in
theorem conj_eq_of_inf_ne_bot_six (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6))
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) {g : G}
    (hne : CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≠ ⊥) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haQ : a ∈ CFSG.Open.pCoreOf 2 M := (Subgroup.mem_inf.1 ha).1
  have haQg : g⁻¹ * a * g ∈ CFSG.Open.pCoreOf 2 M := mem_conjSubgroup.1 (Subgroup.mem_inf.1 ha).2
  have hle := TI.conj_le_TOf (C.Q_comm hR) hH haQ ha1' haQg
  by_cases hl2 : barLen (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩)) = 2
  · obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩))
    rw [hl2] at hIc
    exact D.conj_eq_of_le_TOf_len_two hR halt haQ hIc hI hle
  · have hl4 : barLen (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩)) ≠ 4 := fun h => by
      have := Six.barLen_le_three (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩))
      omega
    have hTQ : TOf M a ≤ CFSG.Open.pCoreOf 2 M := by
      have h1 := D.pCore_centralizer_le_Q_of_len hR ⟨a, haQ⟩ ⟨hl2, hl4⟩
      rw [centralizer_singleton_eq_zpowers a] at h1
      exact h1
    exact Subgroup.eq_of_le_of_card_ge (hle.trans hTQ)
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

include D in
theorem qB_isTI_six (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6))
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    IsTI C.qB := by
  intro g
  by_cases hbot : C.qB ⊓ conjSubgroup g C.qB = ⊥
  · exact Or.inl hbot
  · right
    have hne : CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≠ ⊥ := by
      intro h
      apply hbot
      refine le_bot_iff.1 ?_
      rw [← h]
      exact inf_le_inf C.qB_le_Q fun e he =>
        mem_conjSubgroup.2 (C.qB_le_Q (mem_conjSubgroup.1 he))
    have hQg := D.conj_eq_of_inf_ne_bot_six hR halt hH hne
    have hgM : g ∈ M := by
      rw [← C.S.normalizer_Q_eq]
      exact TI.mem_normalizer_iff_conj.2 hQg
    have hgB : g ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) := by
      rw [C.normalizer_qB_eq hR]
      exact hgM
    rw [TI.mem_normalizer_iff_conj.1 hgB, inf_idem]

theorem qB_ne_bot_six (hR : Nat.card ↥(Rc X) ≤ 2) : C.qB ≠ ⊥ := fun h =>
  C.S.blockU_ne_bot (le_bot_iff.1 (h ▸ C.blockU_le_qB (C.Q_comm hR)))

include D in
theorem qB_weaklyClosed_six (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6))
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    WeaklyClosedIn C.qB (Subgroup.normalizer ((C.qB : Subgroup G) : Set G)) := by
  have hQ := C.Q_comm hR
  refine TI.weaklyClosed_of_cent C.qB_le_Q (qB_ne_bot_six hR) (isPGroup_pCoreOf' M) ?_
    ((C.normalizer_qB_eq hR).trans C.S.normalizer_Q_eq.symm)
    (fun _ hg => D.conj_eq_of_inf_ne_bot_six hR halt hH hg)
  intro c hc
  have hcN : c ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer ((C.qB : Subgroup G) : Set G)
      (Subgroup.mem_centralizer_iff.2 fun b hb => (hc b hb).symm)
  have hcM : c ∈ M := by
    rw [← C.normalizer_qB_eq hR]
    exact hcN
  have hcK : c ∈ C.K :=
    C.mem_K_of_comm_W hcM fun w hw => hc w (C.blockU_le_qB hQ hw)
  rw [C.K_eq_Q hR] at hcK
  exact hcK

include D in
theorem inCatalog_of_centInM_six
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6))
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    CFSG.Assembly.InCatalog G :=
  CFSG.CGT.Hall82.inCatalog_of_isTI_of_weaklyClosedIn hNode C.S.simple C.S.nonab
    (C.isElemAbelian_qB (C.Q_comm hR)) (qB_ne_bot_six hR) (D.qB_isTI_six hR halt hH)
    (D.qB_weaklyClosed_six hR halt hH)

include D in
theorem inCatalog_of_alt
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6))
    (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) : CFSG.Assembly.InCatalog G := by
  refine D.inCatalog_of_centInM_six hNode hR halt fun x hx hx1 => ?_
  by_cases hl2 : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) = 2
  · obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨x, hx⟩))
    rw [hl2] at hIc
    exact D.centralizer_le_M_len_two hR halt hQ16 hx hIc hI
  · have hl4 : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) ≠ 4 := fun h => by
      have := Six.barLen_le_three (Multiplicative.toAdd (D.piQ ⟨x, hx⟩))
      omega
    exact (D.centralizer_le_of_len hR ⟨x, hx⟩ hx1 ⟨hl2, hl4⟩).1

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
