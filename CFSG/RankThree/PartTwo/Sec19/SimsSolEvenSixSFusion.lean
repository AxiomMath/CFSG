module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixST
public import CFSG.CGT.Hall82.TheoremA
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixAlt

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace SixSFusionAux

section Generic

variable {H : Type*} [Group H]

theorem relIndex_dvd_index_of_normal [Finite H] (A N : Subgroup H) [N.Normal] :
    A.relIndex N ∣ A.index := by
  have h1 : (A ⊓ N).relIndex A * A.relIndex (A ⊔ N) =
      (A ⊓ N).relIndex N * N.relIndex (A ⊔ N) := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left,
      Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right]
  have h2 : (A ⊓ N).relIndex A = N.relIndex A := by rw [inf_comm, Subgroup.inf_relIndex_right]
  rw [h2, Subgroup.relIndex_sup_right, Subgroup.inf_relIndex_right,
    mul_comm (A.relIndex N)] at h1
  have h0 : N.relIndex A ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have h3 : A.relIndex (A ⊔ N) = A.relIndex N :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) h1
  rw [← h3]
  exact Subgroup.relIndex_dvd_index_of_le le_sup_left

end Generic

section Group

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_conj_mem {N K : Subgroup G} (hnorm : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) :
    K ≤ Subgroup.normalizer (N : Set G) := fun k hk => by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hnorm k hk n hn, fun hn => ?_⟩
  have := hnorm k⁻¹ (K.inv_mem hk) _ hn
  simpa [mul_assoc] using this

theorem le_of_normal_isPGroup_of_odd_index {N H K : Subgroup G} (hNK : N ≤ K) (hHK : H ≤ K)
    (hnorm : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hN : IsPGroup 2 N)
    (hodd : Odd (H.subgroupOf K).index) : N ≤ H := by
  have hNn : K ≤ Subgroup.normalizer (N : Set G) := le_normalizer_of_conj_mem hnorm
  haveI : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNn
  have h1 := relIndex_dvd_index_of_normal (H.subgroupOf K) (N.subgroupOf K)
  rw [Subgroup.relIndex_subgroupOf hNK] at h1
  have hodd' : Odd (H.relIndex N) := Odd.of_dvd_nat hodd h1
  have h3 : H.relIndex N ∣ Nat.card N := Subgroup.index_dvd_card _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN
  rw [hk] at h3
  have hcop : Nat.Coprime (H.relIndex N) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd')
  have h4 : H.relIndex N = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h3
  exact Subgroup.relIndex_eq_one.1 h4

theorem sup_conj_mem {A B : Subgroup G} {k : G} (hA : ∀ a ∈ A, k * a * k⁻¹ ∈ A)
    (hB : ∀ b ∈ B, k * b * k⁻¹ ∈ B) : ∀ t ∈ A ⊔ B, k * t * k⁻¹ ∈ A ⊔ B := by
  intro t ht
  have hle : (A ⊔ B).map (MulAut.conj k).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hA z hz
    · rintro _ ⟨z, hz, rfl⟩
      exact hB z hz
  exact hle ⟨t, ht, rfl⟩

theorem card_conjSubgroup (g : G) (H : Subgroup G) :
    Nat.card ↥(conjSubgroup g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

end Group

section PiD

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

theorem piQ_surjective_of_not_range
    (hV : ∃ q : ↥(CFSG.Open.pCoreOf 2 M),
      Multiplicative.toAdd (D.piQ q) ∉ Set.range (heartToBar (n := 6))) :
    Function.Surjective D.piQ := by
  obtain ⟨q₀, hq₀⟩ := hV
  intro v
  by_cases hv : Multiplicative.toAdd v ∈ Set.range (heartToBar (n := 6))
  · obtain ⟨u, hu⟩ := hv
    obtain ⟨q, -, hq⟩ := Subgroup.mem_map.1 (D.heart_mem_piQ_Q u)
    refine ⟨q, ?_⟩
    rw [hq]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, hu]
  · obtain ⟨u, hu⟩ := add_mem_range_heartToBar hv hq₀
    obtain ⟨q₁, -, hq₁⟩ := Subgroup.mem_map.1 (D.heart_mem_piQ_Q u)
    refine ⟨q₁ * q₀, ?_⟩
    rw [map_mul, hq₁]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, hu, add_assoc, permBar_add_self, add_zero]

theorem card_Q_eq_of_surjective (hsurj' : Function.Surjective D.piQ) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M) = Nat.card ↥(Rc X) * 32 := by
  have h := D.card_eq_card_inf_R_mul (le_refl (CFSG.Open.pCoreOf 2 M))
  have hRQ : CFSG.Open.pCoreOf 2 M ⊓ Rc X = Rc X := inf_eq_right.2 (by
    rw [C.S.R_eq_inf]
    exact inf_le_left)
  have hmap : ((CFSG.Open.pCoreOf 2 M).subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top.2 hsurj']
  have h32 : Nat.card ↥(⊤ : Subgroup (Multiplicative (permBar 6))) = 32 := by
    rw [Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd : Multiplicative (permBar 6) ≃ _),
      Comb.card_permBar (by norm_num)]
    norm_num
  rw [hRQ, hmap, h32] at h
  exact h

theorem exists_len_one_of_T2 (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj' : Function.Surjective D.piQ)
    {i j : Fin 6} (hij : i ≠ j) {Q' : Subgroup G} (hQ'M : Q' ≤ M)
    (hQ'ab : ∀ a ∈ Q', ∀ b ∈ Q', a * b = b * a)
    (hcard : Nat.card ↥Q' = Nat.card ↥(CFSG.Open.pCoreOf 2 M)) (hQ'T : Q' ≤ C.T2 i j)
    {t : G} (htQ' : t ∈ Q') (htθ : C.θ ⟨t, hQ'M htQ'⟩ = swap i j) :
    ∃ (s : G) (hs : s ∈ CFSG.Open.pCoreOf 2 M), s ∈ Q' ∧
      barLen (Multiplicative.toAdd (D.piQ ⟨s, hs⟩)) = 1 := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  have h1 := C.card_eq_card_inf_mul hR hQ'M
  have hθle : (Q'.subgroupOf M).map C.θ ≤ Subgroup.zpowers (swap i j) := by
    rintro _ ⟨m, hm, rfl⟩
    exact (C.mem_thetaPre.1 (hQ'T hm)).2
  have hθcard : Nat.card ↥((Q'.subgroupOf M).map C.θ) ≤ 2 := by
    have := Subgroup.card_le_of_le hθle
    rwa [Nat.card_zpowers, Equiv.Perm.IsSwap.orderOf ⟨i, j, hij, rfl⟩] at this
  have h2 : Nat.card ↥Q' ≤ Nat.card ↥(Q' ⊓ Q) * 2 := by
    rw [h1]
    exact Nat.mul_le_mul_left _ hθcard
  have h3 := D.card_eq_card_inf_R_mul (H := Q' ⊓ Q) inf_le_right
  have h4 := card_Q_eq_of_surjective D hsurj'
  have h5 : Nat.card ↥((Q' ⊓ Q) ⊓ Rc X) ≤ Nat.card ↥(Rc X) :=
    Subgroup.card_le_of_le inf_le_right
  have hRpos : 0 < Nat.card ↥(Rc X) := Nat.card_pos
  set B : Subgroup (Multiplicative (permBar 6)) := ((Q' ⊓ Q).subgroupOf Q).map D.piQ with hB
  have hB16 : 16 ≤ Nat.card ↥B := by
    by_contra hlt
    push Not at hlt
    have h6 : Nat.card ↥(Q' ⊓ Q) ≤ Nat.card ↥(Rc X) * 15 := by
      rw [h3]
      exact Nat.mul_le_mul h5 (by omega)
    have h7 : Nat.card ↥(Rc X) * 32 ≤ Nat.card ↥(Rc X) * 30 := by
      calc Nat.card ↥(Rc X) * 32 = Nat.card ↥Q := h4.symm
        _ = Nat.card ↥Q' := hcard.symm
        _ ≤ Nat.card ↥(Q' ⊓ Q) * 2 := h2
        _ ≤ (Nat.card ↥(Rc X) * 15) * 2 := Nat.mul_le_mul_right 2 h6
        _ = Nat.card ↥(Rc X) * 30 := by ring
    omega
  have hfix : ∀ x ∈ B, barAct (swap i j) (Multiplicative.toAdd x) = Multiplicative.toAdd x := by
    rintro _ ⟨q, hq, rfl⟩
    have hqQ' : (q : G) ∈ Q' := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)).1
    have hcomm : (q : G) = t * q * t⁻¹ := by
      have := hQ'ab t htQ' q hqQ'
      calc (q : G) = (q * t) * t⁻¹ := by group
        _ = (t * q) * t⁻¹ := by rw [this]
    have h7 := D.piQ_conj ⟨t, hQ'M htQ'⟩ q q hcomm
    rw [htθ] at h7
    exact h7.symm
  let f : ↥B → ↥(Comb.fixSub ({swap i j} : Set (Perm (Fin 6)))) := fun x =>
    ⟨Multiplicative.toAdd (x : Multiplicative (permBar 6)), fun σ hσ => by
      rw [Set.mem_singleton_iff.1 hσ]
      exact hfix x.1 x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h' := congrArg Subtype.val hxy
    exact Subtype.ext (Multiplicative.toAdd.injective h')
  have hcardfix : Nat.card ↥(Comb.fixSub ({swap i j} : Set (Perm (Fin 6)))) = 16 := by
    have := Comb.card_fixSub_swap (by norm_num : 5 ≤ 6) i j hij
    simpa using this
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [hcardfix]; exact hB16)
  obtain ⟨k, hkJ⟩ : ({i, j}ᶜ : Finset (Fin 6)).Nonempty :=
    Finset.card_pos.1 (by rw [SixS.card_compl_pair hij]; norm_num)
  have hki : k ≠ i := by
    rintro rfl
    exact Finset.mem_compl.1 hkJ (by simp)
  have hkj : k ≠ j := by
    rintro rfl
    exact Finset.mem_compl.1 hkJ (by simp)
  have hmem : barInd ({k} : Finset (Fin 6)) ∈ Comb.fixSub ({swap i j} : Set (Perm (Fin 6))) := by
    intro σ hσ
    rw [Set.mem_singleton_iff.1 hσ, barAct_barInd, Finset.image_singleton,
      Equiv.swap_apply_of_ne_of_ne hki hkj]
  obtain ⟨⟨x, hxB⟩, hfx⟩ := hbij.2 ⟨barInd {k}, hmem⟩
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.1 hxB
  have hqinf : (q : G) ∈ Q' ⊓ Q := Subgroup.mem_subgroupOf.1 hq
  refine ⟨q, q.2, (Subgroup.mem_inf.1 hqinf).1, ?_⟩
  have hπq : Multiplicative.toAdd (D.piQ q) = barInd {k} := by
    rw [hqx]
    exact congrArg Subtype.val hfx
  rw [hπq, barLen_barInd, Finset.card_singleton]
  norm_num

include D in
theorem false_of_T1_le (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ)
    {i j : Fin 6} (hij : i ≠ j) {Q' : Subgroup G} (hQ'M : Q' ≤ M)
    (hQ'ab : ∀ a ∈ Q', ∀ b ∈ Q', a * b = b * a)
    (hQnorm : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ u ∈ Q', q * u * q⁻¹ ∈ Q')
    (hT1 : C.T1 i j ≤ Q' ⊔ CFSG.Open.pCoreOf 2 M) : False := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  have hJ : ({i, j}ᶜ : Finset (Fin 6)).card = 4 := SixS.card_compl_pair hij
  have hF := klein4_fourGroup hJ
  have hFbot : klein4 ({i, j}ᶜ : Finset (Fin 6)) ≠ ⊥ := by
    intro h
    have := card_klein4 hJ
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨σ₁, hσ₁F, hσ₁1, -⟩ := hF.exists_ne hJ hFbot 1
  obtain ⟨σ₂, hσ₂F, hσ₂1, hσ₂σ₁⟩ := hF.exists_ne hJ hFbot σ₁
  have hker := C.theta_ker_eq hR
  rw [← hQ] at hker
  have hsup : ((Q' ⊔ Q).subgroupOf M).map C.θ = (Q'.subgroupOf M).map C.θ := by
    have h1 : (Q' ⊔ Q).subgroupOf M = Q'.subgroupOf M ⊔ Q.subgroupOf M :=
      (Subgroup.comap_sup_eq_of_le_range M.subtype (by rw [Subgroup.range_subtype]; exact hQ'M)
        (by rw [Subgroup.range_subtype]; exact pCoreOf_le_self M)).symm
    have h2 : (Q.subgroupOf M).map C.θ = ⊥ := (Subgroup.map_eq_bot_iff _).2 hker.ge
    rw [h1, Subgroup.map_sup, h2, sup_bot_eq]
  have hθ : ∀ σ ∈ klein4 ({i, j}ᶜ : Finset (Fin 6)), ∃ p : ↥M, (p : G) ∈ Q' ∧ C.θ p = σ := by
    intro σ hσ
    obtain ⟨m, hm⟩ := hsurj σ
    have hmT1 : (m : G) ∈ C.T1 i j := C.mem_thetaPre.2 ⟨m.2, by
      rw [show (⟨(m : G), m.2⟩ : ↥M) = m from rfl, hm]
      exact hσ⟩
    have hmN : m ∈ (Q' ⊔ Q).subgroupOf M := hT1 hmT1
    have : σ ∈ ((Q' ⊔ Q).subgroupOf M).map C.θ := ⟨m, hmN, hm⟩
    rw [hsup] at this
    obtain ⟨p, hp, hpσ⟩ := this
    exact ⟨p, hp, hpσ⟩
  obtain ⟨p₁, hp₁, hθ₁⟩ := hθ σ₁ hσ₁F
  obtain ⟨p₂, hp₂, hθ₂⟩ := hθ σ₂ hσ₂F
  obtain ⟨d, hdQ', hd⟩ := D.exists_not_comm_of_fourGroup hJ hF hQnorm hp₁ hp₂
    (by rw [hθ₁]; exact hσ₁F) (by rw [hθ₁]; exact hσ₁1) (by rw [hθ₂]; exact hσ₂F)
    (by rw [hθ₂]; exact hσ₂1) (by rw [hθ₁, hθ₂]; exact fun h => hσ₂σ₁ h.symm)
  exact hd (hQ'ab _ hp₁ d hdQ')

end PiD

end SixSFusionAux

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

theorem mem_M_of_conj_len_odd (hR : Nat.card ↥(Rc X) ≤ 2) {y : G}
    (hy : y ∈ CFSG.Open.pCoreOf 2 M) (hl0 : barLen (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) ≠ 0)
    (hl2 : barLen (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) ≠ 2) {g : G}
    (hg : g * y * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : g ∈ M := by
  classical
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hl0
    have : (⟨1, hy⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 := rfl
    rw [this, map_one, toAdd_one]
    exact Comb.barLen_zero
  have hl3 := SixS.barLen_le_three (Multiplicative.toAdd (D.piQ ⟨y, hy⟩))
  have hl4 : barLen (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) ≠ 4 := by omega
  by_cases hl' : barLen (Multiplicative.toAdd (D.piQ ⟨g * y * g⁻¹, hg⟩)) = 2
  · exfalso
    obtain ⟨hCy, -⟩ := D.centralizer_le_of_len hR ⟨y, hy⟩ hy1 ⟨hl2, hl4⟩
    have hCy' : CGOf y ≤ M := by rwa [centralizer_singleton_eq_zpowers] at hCy
    have hCM : CMOf M y = CGOf y := inf_eq_right.2 hCy'
    have hcard : Nat.card ↥(CGOf (g * y * g⁻¹)) = Nat.card ↥(CGOf y) := by
      rw [H4b.CGOf_conj]
      exact SixSFusionAux.card_conjSubgroup g _
    have h15 := D.card_M_eq_fifteen hR hg hl'
    obtain ⟨k, hk, hMk⟩ := D.card_M_eq_CMOf_six hR ⟨y, hy⟩
    simp only at hMk
    rw [hCM] at hMk
    have hdvd : Nat.card ↥(CMOf M (g * y * g⁻¹)) ∣ Nat.card ↥(CGOf y) := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨s, hs⟩ := hdvd
    have hpos : 0 < Nat.card ↥(CMOf M (g * y * g⁻¹)) := Nat.card_pos
    rcases SixS.card_barLen_cases (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) with
        ⟨hla, -⟩ | ⟨hla, ho⟩ | ⟨hla, -⟩ | ⟨hla, ho⟩
    · exact hl0 hla
    · rw [ho] at hMk
      have e : 15 * Nat.card ↥(CMOf M (g * y * g⁻¹)) =
          (6 * k * s) * Nat.card ↥(CMOf M (g * y * g⁻¹)) := by
        rw [← h15, hMk, hs]
        ring
      have e' := Nat.eq_of_mul_eq_mul_right hpos e
      rcases hk with rfl | rfl <;> omega
    · exact hl2 hla
    · rw [ho] at hMk
      have e : 15 * Nat.card ↥(CMOf M (g * y * g⁻¹)) =
          (10 * k * s) * Nat.card ↥(CMOf M (g * y * g⁻¹)) := by
        rw [← h15, hMk, hs]
        ring
      have e' := Nat.eq_of_mul_eq_mul_right hpos e
      rcases hk with rfl | rfl <;> omega
  · have hy'1 : g * y * g⁻¹ ≠ 1 := by
      intro h
      apply hy1
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this, h]
      group
    have hl'4 : barLen (Multiplicative.toAdd (D.piQ ⟨g * y * g⁻¹, hg⟩)) ≠ 4 := by
      have := SixS.barLen_le_three (Multiplicative.toAdd (D.piQ ⟨g * y * g⁻¹, hg⟩))
      omega
    exact D.mem_of_conj_of_len hR (x := ⟨y, hy⟩) (y := ⟨g * y * g⁻¹, hg⟩) hy1 hy'1
      ⟨hl2, hl4⟩ ⟨hl', hl'4⟩ rfl

theorem mem_M_of_conj_R_heart (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ)
    (hU : ∀ q : ↥(CFSG.Open.pCoreOf 2 M),
      Multiplicative.toAdd (D.piQ q) ∈ Set.range (heartToBar (n := 6)))
    {r : G} (hr : r ∈ Rc X) (hr1 : r ≠ 1) {g : G}
    (hg : g * r * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : g ∈ M := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  have hRQ : Rc X ≤ Q := by
    rw [C.S.R_eq_inf]
    exact inf_le_left
  have hrQ : r ∈ Q := hRQ hr
  have hrr : r * r = 1 := Rc_mul_self hR hr
  have hRz : Rc X = Subgroup.zpowers r := by
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 hr)
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have : x = r := congrArg Subtype.val (eq_of_card_le_two hR (a := ⟨x, hx⟩) (b := ⟨r, hr⟩)
        (fun h => hx1 (congrArg Subtype.val h)) (fun h => hr1 (congrArg Subtype.val h)))
      rw [this]
      exact Subgroup.mem_zpowers r
  have hCr : Subgroup.centralizer ({r} : Set G) = M := by
    refine le_antisymm (C.S.centralizer_le_of_mem_R hr hr1) fun m hm => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := C.S.R_central hR hm hr
    calc m * r = (m * r * m⁻¹) * m := by group
      _ = r * m := by rw [this]
  have hU' : ∀ q : ↥Q, ∃ a : altHeart 6, heartToBar a = Multiplicative.toAdd (D.piQ q) := hU
  choose f hf using hU'
  let π' : ↥Q →* Multiplicative (altHeart 6) :=
    { toFun := fun q => Multiplicative.ofAdd (f q)
      map_one' := by
        apply Multiplicative.toAdd.injective
        show f 1 = 0
        apply heartToBar_injective
        rw [hf, map_one, toAdd_one, map_zero]
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        show f (a * b) = f a + f b
        apply heartToBar_injective
        rw [map_add, hf, hf, hf, map_mul, toAdd_mul] }
  have hπ'spec : ∀ q : ↥Q, heartToBar (Multiplicative.toAdd (π' q)) =
      Multiplicative.toAdd (D.piQ q) := hf
  have hsurj' : Function.Surjective π' := by
    intro a
    obtain ⟨q, -, hq⟩ := Subgroup.mem_map.1 (D.heart_mem_piQ_Q (Multiplicative.toAdd a))
    refine ⟨q, ?_⟩
    apply Multiplicative.toAdd.injective
    apply heartToBar_injective
    rw [hπ'spec, hq]
    rfl
  have hker : π'.ker = (Subgroup.zpowers r).subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hRz, ← D.piQ_eq_one_iff]
    constructor
    · intro h
      apply Multiplicative.toAdd.injective
      rw [toAdd_one, ← hπ'spec, h, toAdd_one, map_zero]
    · intro h
      apply Multiplicative.toAdd.injective
      apply heartToBar_injective
      rw [hπ'spec, h, toAdd_one, toAdd_one, map_zero]
  have hequiv : ∀ (m : ↥M) (q q' : ↥Q), (q' : G) = m * q * m⁻¹ →
      Multiplicative.toAdd (π' q') = altAct (C.θ m) (Multiplicative.toAdd (π' q)) := by
    intro m q q' h
    apply heartToBar_injective
    rw [hπ'spec, D.piQ_conj m q q' h, heartToBar_altAct, hπ'spec]
  obtain ⟨-, -, hwc, -⟩ := CFSG.CGT.Hall82.TheoremA.hallTheoremANat_holds G M C.θ r π' hsurj
    (C.theta_ker_eq hR) hrQ hr1 hrr
    (fun m hm => mul_inv_eq_iff_eq_mul.1 (C.S.R_central hR hm hr)) hsurj' hker hequiv
    C.S.normalizer_Q_eq hCr
  have hgle : conjSubgroup g (Subgroup.zpowers r) ≤ Q := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_conjSubgroup.1 hx)
    have : x = (g * r * g⁻¹) ^ k := by
      rw [conj_zpow]
      have h1 : g⁻¹ * x * g = r ^ k := hk.symm
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * r ^ k * g⁻¹ := by rw [h1]
    rw [this]
    exact Q.zpow_mem hg k
  have heq := hwc.2 g hgle
  have hmem : g * r * g⁻¹ ∈ Subgroup.zpowers r := by
    have : g * r * g⁻¹ ∈ conjSubgroup g (Subgroup.zpowers r) := by
      rw [mem_conjSubgroup]
      have e : g⁻¹ * (g * r * g⁻¹) * g = r := by group
      rw [e]
      exact Subgroup.mem_zpowers r
    rwa [heq] at this
  rw [← hRz] at hmem
  have hne1 : g * r * g⁻¹ ≠ 1 := by
    intro h
    apply hr1
    have : r = g⁻¹ * (g * r * g⁻¹) * g := by group
    rw [this, h]
    group
  have hgr : g * r * g⁻¹ = r := congrArg Subtype.val (eq_of_card_le_two hR (a := ⟨_, hmem⟩)
    (b := ⟨r, hr⟩) (fun h => hne1 (congrArg Subtype.val h)) (fun h => hr1 (congrArg Subtype.val h)))
  rw [← hCr, Subgroup.mem_centralizer_singleton_iff]
  calc g * r = (g * r * g⁻¹) * g := by group
    _ = r * g := by rw [hgr]

theorem mem_M_of_conj_R_bar (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ)
    (hV : ∃ q : ↥(CFSG.Open.pCoreOf 2 M),
      Multiplicative.toAdd (D.piQ q) ∉ Set.range (heartToBar (n := 6)))
    {r : G} (hr : r ∈ Rc X) (hr1 : r ≠ 1) {g : G}
    (hg : g * r * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : g ∈ M := by
  classical
  by_contra hgM
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  have hQab := C.Q_comm hR
  have hRQ : Rc X ≤ Q := by
    rw [C.S.R_eq_inf]
    exact inf_le_left
  have hCr : Subgroup.centralizer ({r} : Set G) = M := by
    refine le_antisymm (C.S.centralizer_le_of_mem_R hr hr1) fun m hm => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := C.S.R_central hR hm hr
    calc m * r = (m * r * m⁻¹) * m := by group
      _ = r * m := by rw [this]
  have hsurj' : Function.Surjective D.piQ := SixSFusionAux.piQ_surjective_of_not_range D hV
  set y : G := g * r * g⁻¹ with hy
  have hyR : y ∉ Rc X := by
    intro hyR
    have hy1 : y ≠ 1 := by
      intro h
      apply hr1
      have : r = g⁻¹ * y * g := by rw [hy]; group
      rw [this, h]
      group
    have hyr : y = r := congrArg Subtype.val (eq_of_card_le_two hR (a := ⟨y, hyR⟩) (b := ⟨r, hr⟩)
      (fun h => hy1 (congrArg Subtype.val h)) (fun h => hr1 (congrArg Subtype.val h)))
    apply hgM
    rw [← hCr, Subgroup.mem_centralizer_singleton_iff]
    calc g * r = (g * r * g⁻¹) * g := by group
      _ = r * g := by rw [← hy, hyr]
  have hl0 : barLen (Multiplicative.toAdd (D.piQ ⟨y, hg⟩)) ≠ 0 := by
    intro h0
    apply hyR
    have h1 : D.piQ ⟨y, hg⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [eq_zero_of_barLen_eq_zero h0]
      rfl
    exact (D.piQ_eq_one_iff _).1 h1
  have hl2 : barLen (Multiplicative.toAdd (D.piQ ⟨y, hg⟩)) = 2 := by
    by_contra hl2
    have hrQ' : g⁻¹ * y * g⁻¹⁻¹ ∈ Q := by
      have : g⁻¹ * y * g⁻¹⁻¹ = r := by rw [hy]; group
      rw [this]
      exact hRQ hr
    exact hgM (by simpa using M.inv_mem (D.mem_M_of_conj_len_odd hR hg hl0 hl2 hrQ'))
  obtain ⟨I, hIc, hIπ⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨y, hg⟩))
  rw [hl2] at hIc
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hIc
  have hK : CGOf y = conjSubgroup g M := by
    have e : CGOf r = M := by
      show Subgroup.centralizer ((Subgroup.zpowers r : Subgroup G) : Set G) = M
      rw [← centralizer_singleton_eq_zpowers, hCr]
    rw [hy, H4b.CGOf_conj, e]
  set Q' : Subgroup G := conjSubgroup g Q with hQ'
  have hcardQ' : Nat.card ↥Q' = Nat.card ↥Q := SixSFusionAux.card_conjSubgroup g Q
  have hQ'2 : IsPGroup 2 ↥Q' := (isPGroup_pCoreOf' M).map (MulAut.conj g).toMonoidHom
  have hQ'K : Q' ≤ CGOf y := by
    rw [hK]
    exact Subgroup.map_mono (pCoreOf_le_self M)
  have hKnorm : ∀ k ∈ CGOf y, ∀ q' ∈ Q', k * q' * k⁻¹ ∈ Q' := by
    intro k hk q' hq'
    rw [hK, mem_conjSubgroup] at hk
    rw [mem_conjSubgroup] at hq' ⊢
    have e : g⁻¹ * (k * q' * k⁻¹) * g = (g⁻¹ * k * g) * (g⁻¹ * q' * g) * (g⁻¹ * k * g)⁻¹ := by
      group
    rw [e]
    exact pCoreOf_normalized M hk hq'
  have hQ'ab : ∀ a ∈ Q', ∀ b ∈ Q', a * b = b * a := by
    intro a ha b hb
    have h1 := hQab _ (mem_conjSubgroup.1 ha) _ (mem_conjSubgroup.1 hb)
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = b * a := by group
  have hQ'ne : Q' ≠ Q := fun h => hgM (by
    rw [← C.S.normalizer_Q_eq]
    exact TI.mem_normalizer_iff_conj.2 h)
  have hH : CMOf M y ≤ CGOf y := inf_le_right
  have hodd : Odd ((CMOf M y).subgroupOf (CGOf y)).index := by
    have h15 := D.card_M_eq_fifteen hR hg hl2
    have hcardK : Nat.card ↥(CGOf y) = Nat.card ↥M := by
      rw [hK]
      exact SixSFusionAux.card_conjSubgroup g M
    have hidx := Subgroup.card_mul_index ((CMOf M y).subgroupOf (CGOf y))
    have hcardsub : Nat.card ↥((CMOf M y).subgroupOf (CGOf y)) = Nat.card ↥(CMOf M y) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
    rw [hcardsub, hcardK, h15] at hidx
    have hpos : 0 < Nat.card ↥(CMOf M y) := Nat.card_pos
    have h2 : ((CMOf M y).subgroupOf (CGOf y)).index = 15 :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [hidx]; ring)
    rw [h2]
    decide
  have hQ'C : Q' ≤ CMOf M y :=
    SixSFusionAux.le_of_normal_isPGroup_of_odd_index hQ'K hH hKnorm hQ'2 hodd
  have hQ'M : Q' ≤ M := hQ'C.trans inf_le_left
  have hQC : Q ≤ CMOf M y := fun q hq => Subgroup.mem_inf.2 ⟨pCoreOf_le_self M hq,
    mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 (hQab q hq y hg))⟩
  have hQnorm : ∀ q ∈ Q, ∀ u ∈ Q', q * u * q⁻¹ ∈ Q' := fun q hq u hu =>
    hKnorm q (hQC hq).2 u hu
  have hNn' : Q ≤ Subgroup.normalizer (Q' : Set G) :=
    SixSFusionAux.le_normalizer_of_conj_mem hQnorm
  have hN2 : IsPGroup 2 ↥(Q' ⊔ Q : Subgroup G) :=
    hQ'2.to_sup_of_normal_left' (isPGroup_pCoreOf' M) hNn'
  have hNC : Q' ⊔ Q ≤ CMOf M y := sup_le hQ'C hQC
  have hNnorm : ∀ k ∈ CMOf M y, ∀ t ∈ Q' ⊔ Q, k * t * k⁻¹ ∈ Q' ⊔ Q := fun k hk =>
    SixSFusionAux.sup_conj_mem (hKnorm k (Subgroup.mem_inf.1 hk).2)
      (fun b hb => pCoreOf_normalized M (Subgroup.mem_inf.1 hk).1 hb)
  have hNT : Q' ⊔ Q ≤ TOf M y := le_pCoreOf_of_normalized hNC hNnorm hN2
  rcases D.normal_cases hR hsurj hg hij hIπ (N := Q' ⊔ Q) le_sup_right hNT hNnorm with
    hN | hN | hN | hN
  ·
    have hle : Q' ≤ Q := le_sup_left.trans hN.le
    exact hQ'ne (Subgroup.eq_of_le_of_card_ge hle hcardQ'.ge)
  ·
    have hQ'T : Q' ≤ C.T2 i j := le_sup_left.trans hN.le
    have ht : ∃ t ∈ Q', ∃ htM : t ∈ M, C.θ ⟨t, htM⟩ = swap i j := by
      by_contra hcon
      push Not at hcon
      have hQ'Q : Q' ≤ Q := by
        intro p hp
        have hpM := hQ'M hp
        obtain ⟨hpM', hpθ⟩ := C.mem_thetaPre.1 (hQ'T hp)
        rcases SixS.mem_zpowers_swap hpθ with h1 | h1
        · have h2 : (⟨p, hpM⟩ : ↥M) ∈ C.θ.ker := MonoidHom.mem_ker.2 h1
          rw [C.theta_ker_eq hR] at h2
          exact h2
        · exact absurd h1 (hcon p hp hpM)
      exact hQ'ne (Subgroup.eq_of_le_of_card_ge hQ'Q hcardQ'.ge)
    obtain ⟨t, htQ', htM, htθ⟩ := ht
    obtain ⟨s, hsQ, hsQ', hs1⟩ := SixSFusionAux.exists_len_one_of_T2 D hR hsurj' hij hQ'M hQ'ab
      hcardQ' hQ'T htQ' htθ
    have hgs : g⁻¹ * s * g⁻¹⁻¹ ∈ Q := by simpa using mem_conjSubgroup.1 hsQ'
    have hl0' : barLen (Multiplicative.toAdd (D.piQ ⟨s, hsQ⟩)) ≠ 0 := by
      rw [hs1]
      norm_num
    have hl2' : barLen (Multiplicative.toAdd (D.piQ ⟨s, hsQ⟩)) ≠ 2 := by
      rw [hs1]
      norm_num
    exact hgM (by simpa using M.inv_mem (D.mem_M_of_conj_len_odd hR hsQ hl0' hl2' hgs))
  ·
    exact SixSFusionAux.false_of_T1_le D hR hsurj hij hQ'M hQ'ab hQnorm hN.ge
  ·
    exact SixSFusionAux.false_of_T1_le D hR hsurj hij hQ'M hQ'ab hQnorm
      ((D.T1_le_TOf hR hsurj hg hij hIπ).trans hN.ge)

theorem mem_M_of_conj_len_ne_two (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ)
    {y : G} (hy : y ∈ CFSG.Open.pCoreOf 2 M) (hy1 : y ≠ 1)
    (hl : barLen (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) ≠ 2) {g : G}
    (hg : g * y * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : g ∈ M := by
  by_cases hl0 : barLen (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) = 0
  · have hyR : y ∈ Rc X := by
      have h0 := eq_zero_of_barLen_eq_zero hl0
      have h1 : D.piQ ⟨y, hy⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0]
        rfl
      exact (D.piQ_eq_one_iff _).1 h1
    by_cases hU : ∀ q : ↥(CFSG.Open.pCoreOf 2 M),
        Multiplicative.toAdd (D.piQ q) ∈ Set.range (heartToBar (n := 6))
    · exact D.mem_M_of_conj_R_heart hR hsurj hU hyR hy1 hg
    · push Not at hU
      exact D.mem_M_of_conj_R_bar hR hsurj hU hyR hy1 hg
  · exact D.mem_M_of_conj_len_odd hR hy hl0 hl hg

theorem mem_M_of_conj_len_two (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ)
    {y : G} (hy : y ∈ CFSG.Open.pCoreOf 2 M)
    (hl : barLen (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) = 2) (hyC : CGOf y ≤ M) {g : G}
    (hg : g * y * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : g ∈ M := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  have hQab := C.Q_comm hR
  have hy1 : y ≠ 1 := by
    rintro rfl
    have h0 : (⟨1, hy⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 := rfl
    rw [h0, map_one, toAdd_one, Comb.barLen_zero] at hl
    exact absurd hl (by norm_num)
  set a : G := g * y * g⁻¹ with ha
  have ha1 : a ≠ 1 := by
    intro h
    apply hy1
    have : y = g⁻¹ * a * g := by rw [ha]; group
    rw [this, h]
    group
  by_cases hla : barLen (Multiplicative.toAdd (D.piQ ⟨a, hg⟩)) = 2
  swap
  ·
    have hyQ' : g⁻¹ * a * g⁻¹⁻¹ ∈ Q := by
      have : g⁻¹ * a * g⁻¹⁻¹ = y := by rw [ha]; group
      rw [this]
      exact hy
    have h1 := D.mem_M_of_conj_len_ne_two hR hsurj hg ha1 hla hyQ'
    simpa using M.inv_mem h1
  have hCMy : CMOf M y = CGOf y := inf_eq_right.2 hyC
  have hcardCa : Nat.card ↥(CGOf a) = Nat.card ↥(CGOf y) := by
    rw [ha, H4b.CGOf_conj]
    exact SixSFusionAux.card_conjSubgroup g _
  have h15y := D.card_M_eq_fifteen hR hy hl
  have h15a := D.card_M_eq_fifteen hR hg hla
  have hCa : CGOf a ≤ M := by
    have hle : CMOf M a ≤ CGOf a := inf_le_right
    have hcard : Nat.card ↥(CMOf M a) = Nat.card ↥(CMOf M y) := by omega
    have heq : CMOf M a = CGOf a := Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcardCa, ← hCMy, hcard])
    rw [← heq]
    exact inf_le_left
  have hCMa : CMOf M a = CGOf a := inf_eq_right.2 hCa
  obtain ⟨σ, hσA, hσ⟩ := SixS.exists_alt_barAct_eq
    (u := Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) (v := Multiplicative.toAdd (D.piQ ⟨a, hg⟩))
    (hl.trans hla.symm)
  obtain ⟨c, hcθ⟩ := C.exists_lift hσA
  have hcM : (c : G) ∈ M := C.S.le c.2
  have hcyQ : (c : G) * y * (c : G)⁻¹ ∈ Q := pCoreOf_normalized M hcM hy
  have hπ : D.piQ ⟨(c : G) * y * (c : G)⁻¹, hcyQ⟩ = D.piQ ⟨a, hg⟩ := by
    apply Multiplicative.toAdd.injective
    rw [D.piQ_conj ⟨(c : G), hcM⟩ ⟨y, hy⟩ _ rfl,
      show C.θ ⟨(c : G), hcM⟩ = σ from hcθ, hσ]
  set h : G := (c : G) * g⁻¹ with hh
  have hha : h * a * h⁻¹ = (c : G) * y * (c : G)⁻¹ := by rw [hh, ha]; group
  have hgh : g = h⁻¹ * (c : G) := by rw [hh]; group
  suffices hhM : h ∈ M by
    rw [hgh]
    exact M.mul_mem (M.inv_mem hhM) hcM
  set ρ : G := a⁻¹ * (h * a * h⁻¹) with hρdef
  have hρR : ρ ∈ Rc X := by
    have h1 : D.piQ (⟨a, hg⟩⁻¹ * ⟨(c : G) * y * (c : G)⁻¹, hcyQ⟩) = 1 := by
      rw [map_mul, map_inv, hπ, inv_mul_cancel]
    have h2' := (D.piQ_eq_one_iff _).1 h1
    have e : ((⟨a, hg⟩⁻¹ * ⟨(c : G) * y * (c : G)⁻¹, hcyQ⟩ : ↥Q) : G) = ρ := by
      rw [hρdef, hha]
      rfl
    rwa [e] at h2'
  have hhaρ : h * a * h⁻¹ = a * ρ := by rw [hρdef]; group
  by_cases hρ1 : ρ = 1
  ·
    have hc : h * a * h⁻¹ = a := by rw [hhaρ, hρ1, mul_one]
    exact hCa (mem_centralizer_zpowers_iff.2 hc)
  ·
    have hRQ : Rc X ≤ Q := by
      rw [C.S.R_eq_inf]
      exact inf_le_left
    have hρQ : ρ ∈ Q := hRQ hρR
    have hCaρ : CGOf (a * ρ) ≤ M := by
      have e : a * ρ = (c : G) * y * (c : G)⁻¹ := by rw [← hhaρ, hha]
      rw [e, H4b.CGOf_conj]
      intro z hz
      have hz' : (c : G)⁻¹ * z * (c : G) ∈ CGOf y := mem_conjSubgroup.1 hz
      have hzM : (c : G)⁻¹ * z * (c : G) ∈ M := hyC hz'
      have : z = (c : G) * ((c : G)⁻¹ * z * (c : G)) * (c : G)⁻¹ := by group
      rw [this]
      exact M.mul_mem (M.mul_mem hcM hzM) (M.inv_mem hcM)
    have hCeq : CGOf (a * ρ) = CGOf a :=
      H4b.CGOf_eq_of_mem_R (C := C) hR hCa hCaρ hρR rfl
    have hnorm : conjSubgroup h (CGOf a) = CGOf a := by
      rw [← H4b.CGOf_conj, hhaρ, hCeq]
    set P : Subgroup G := CFSG.Open.pCoreOf 2 (CGOf a) with hP
    have hhP : ∀ p ∈ P, h * p * h⁻¹ ∈ P := by
      intro p hp
      have h1 : h * p * h⁻¹ ∈ conjSubgroup h P := by
        rw [mem_conjSubgroup]
        have : h⁻¹ * (h * p * h⁻¹) * h = p := by group
        rw [this]
        exact hp
      have h2'' := H4b.conj_pCoreOf_le h (CGOf a) h1
      rwa [hnorm] at h2''
    have hQP : Q ≤ P := by
      have := Q_le_TOf hQab hg
      have e : TOf M a = P := by
        show CFSG.Open.pCoreOf 2 (CMOf M a) = _
        rw [hCMa]
      rwa [e] at this
    have hconjP : conjSubgroup h P = P := by
      have hle : conjSubgroup h P ≤ P := by
        intro w hw
        have h1 := hhP _ (mem_conjSubgroup.1 hw)
        have e : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
        rwa [e] at h1
      exact Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
    have hhinv : ∀ p ∈ P, h⁻¹ * p * h ∈ P := by
      intro p hp
      have h1 : p ∈ conjSubgroup h P := by rw [hconjP]; exact hp
      exact mem_conjSubgroup.1 h1
    set ρ' : G := h * ρ * h⁻¹ with hρ'
    have hρ'Q : ρ' ∈ Q := by
      have hCQ := C.centralizer_Q_eq hR
      rw [← hQ] at hCQ
      rw [← hCQ, Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : h⁻¹ * q * h ∈ P := hhinv q (hQP hq)
      have hqM : h⁻¹ * q * h ∈ M := hCa (pCoreOf_le_self _ hq')
      have hc := C.R_central hR _ hqM ρ hρR
      calc q * ρ' = h * ((h⁻¹ * q * h) * ρ * (h⁻¹ * q * h)⁻¹) * h⁻¹ * q := by
            rw [hρ']; group
        _ = h * ρ * h⁻¹ * q := by rw [hc]
        _ = ρ' * q := by rw [hρ']
    have hlρ : barLen (Multiplicative.toAdd (D.piQ ⟨ρ, hρQ⟩)) ≠ 2 := by
      have h1 : D.piQ ⟨ρ, hρQ⟩ = 1 := (D.piQ_eq_one_iff _).2 hρR
      rw [h1, toAdd_one, Comb.barLen_zero]
      norm_num
    exact D.mem_M_of_conj_len_ne_two hR hsurj hρQ hρ1 hlρ hρ'Q

theorem exists_sylow_le_M (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := C.exists_piData C.six_le C.even_n
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  have hR : Nat.card ↥(Rc X) ≤ 2 := hR2.le
  have hRQ : Rc X ≤ Q := by
    rw [C.S.R_eq_inf]
    exact inf_le_left
  have hRbot : Rc X ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hR2
    omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRbot
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrQ : r ∈ Q := hRQ hr
  let S₀ : Set (Subgroup G) := {P | P ≤ M ∧ IsPGroup 2 ↥P}
  have hS₀ne : S₀.Nonempty := ⟨⊥, bot_le, IsPGroup.of_bot⟩
  obtain ⟨P, ⟨hPM, hP2⟩, hPmax⟩ :=
    Set.exists_max_image S₀ (fun P : Subgroup G => Nat.card ↥P) (Set.toFinite S₀) hS₀ne
  have hQP : Q ≤ P := by
    have hPn : P ≤ Subgroup.normalizer (Q : Set G) := by
      rw [C.S.normalizer_Q_eq]
      exact hPM
    have h2 : IsPGroup 2 ↥(P ⊔ Q : Subgroup G) :=
      hP2.to_sup_of_normal_right' (isPGroup_pCoreOf' M) hPn
    have hle : P ⊔ Q ≤ M := sup_le hPM (pCoreOf_le_self M)
    have hcard := hPmax (P ⊔ Q) ⟨hle, h2⟩
    have heq : P = P ⊔ Q := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    calc Q ≤ P ⊔ Q := le_sup_right
      _ = P := heq.symm
  have hN : ∀ g ∈ Subgroup.normalizer (P : Set G), g ∈ M := by
    intro g hg
    have hgP : ∀ p, p ∈ P ↔ g * p * g⁻¹ ∈ P := Subgroup.mem_normalizer_iff.1 hg
    have hgQM : ∀ q ∈ Q, g * q * g⁻¹ ∈ M := fun q hq => hPM ((hgP q).1 (hQP hq))
    have hCQ := C.centralizer_Q_eq hR
    rw [← hQ] at hCQ
    have hinQ : g⁻¹ * r * g ∈ Q := by
      rw [← hCQ, Subgroup.mem_centralizer_iff]
      intro q hq
      have hc := C.S.R_central hR (hgQM q hq) hr
      calc q * (g⁻¹ * r * g) = g⁻¹ * ((g * q * g⁻¹) * r * (g * q * g⁻¹)⁻¹) * g * q := by group
        _ = g⁻¹ * r * g * q := by rw [hc]
    have hlr : barLen (Multiplicative.toAdd (D.piQ ⟨r, hrQ⟩)) ≠ 2 := by
      have h1 : D.piQ ⟨r, hrQ⟩ = 1 := (D.piQ_eq_one_iff _).2 hr
      rw [h1, toAdd_one, Comb.barLen_zero]
      norm_num
    have h1 := D.mem_M_of_conj_len_ne_two hR hsurj hrQ hr1' hlr (g := g⁻¹) (by simpa using hinQ)
    simpa using M.inv_mem h1
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hSP : (S : Subgroup G) = P := by
    by_contra hne
    obtain ⟨t, htS, htP, htN⟩ := exists_mem_normalizer_of_lt S.isPGroup' hPS (Ne.symm hne)
    have htM : t ∈ M := hN t htN
    have h2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers t : Subgroup G) :=
      isPGroup_of_le S.isPGroup' (sup_le hPS (Subgroup.zpowers_le.2 htS))
    have hle : P ⊔ Subgroup.zpowers t ≤ M := sup_le hPM (Subgroup.zpowers_le.2 htM)
    have hcard := hPmax _ ⟨hle, h2⟩
    have heq : P = P ⊔ Subgroup.zpowers t := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    exact htP (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  exact ⟨S, hSP ▸ hPM⟩

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
