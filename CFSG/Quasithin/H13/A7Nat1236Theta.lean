module

public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Star
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Cases
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Quasithin.H13.A7SharedCubicSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEPerm

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Theta

variable {G : Type} [Group G]

theorem theta_mono {A B : Subgroup G} (h : A ≤ B) : thetaOf A ≤ thetaOf B :=
  closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem conj_mem_theta {A : Subgroup G} {g x : G} (hg : g ∈ normalizer (A : Set G))
    (hx : x ∈ thetaOf A) : g * x * g⁻¹ ∈ thetaOf A := by
  have : thetaOf A ≤ (thetaOf A).comap (MulAut.conj g).toMonoidHom := by
    refine (closure_le _).2 fun y hy => ?_
    show g * y * g⁻¹ ∈ thetaOf A
    refine subset_closure ⟨(mem_normalizer_iff.1 hg y).1 hy.1, ?_⟩
    rw [← hy.2]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
  exact this hx

theorem le_thetaOf_of_simple_quotient {L : Subgroup G}
    (hL1 : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤)
    {S : Type*} [Group S] [IsSimpleGroup S] (α : ↥L →* S) (hα : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) {z : G} (hzL : z ∈ L) (hz3 : orderOf z = 3) :
    L ≤ thetaOf L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W' : Subgroup ↥L := (thetaOf L).subgroupOf L with hW'
  have hnormal : W'.Normal := ⟨fun w hw g => by
    rw [hW', mem_subgroupOf] at hw ⊢
    show (g : G) * (w : G) * (g : G)⁻¹ ∈ thetaOf L
    exact conj_mem_theta (le_normalizer g.2) hw⟩
  have hN : (W'.map α).Normal := hnormal.map α hα
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W'.map α) with h | h
  · exfalso
    have hz : (⟨z, hzL⟩ : ↥L) ∈ W' := by
      rw [hW', mem_subgroupOf]
      exact subset_closure ⟨hzL, hz3⟩
    have h1 : α ⟨z, hzL⟩ = 1 := by
      have : α ⟨z, hzL⟩ ∈ W'.map α := mem_map_of_mem α hz
      rw [h] at this
      exact mem_bot.1 this
    have h2 : (⟨z, hzL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by rw [← hαk]; exact h1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, h2⟩
    have hk' : z ^ 2 ^ k = 1 := by
      have := congrArg (fun x : CFSG.pCore 2 ↥L => ((x : ↥L) : G)) hk
      simpa using this
    have h3 := orderOf_dvd_of_pow_eq_one hk'
    rw [hz3] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · intro l hl
    have hq : IsPGroup 2 (↥L ⧸ W') := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have : α g ∈ W'.map α := by rw [h]; trivial
      obtain ⟨w, hw, hwg⟩ := this
      have hp : (w⁻¹ * g) ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwg, inv_mul_cancel]
      rw [hαk] at hp
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨w⁻¹ * g, hp⟩
      refine ⟨k, ?_⟩
      have hk' : (w⁻¹ * g) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have hq1 : (QuotientGroup.mk (w⁻¹ * g) : ↥L ⧸ W') = QuotientGroup.mk g := by
        rw [QuotientGroup.eq]
        have := hnormal.conj_mem w hw g⁻¹
        simpa [mul_assoc] using this
      rw [← hq1, ← QuotientGroup.mk_pow, hk']
      rfl
    have htop := hL1 W' hq
    have : (⟨l, hl⟩ : ↥L) ∈ W' := by rw [htop]; trivial
    exact mem_subgroupOf.1 this

theorem exists_orderOf_three_alternating {m : ℕ} (hm : 3 ≤ m) :
    ∃ σ : alternatingGroup (Fin m), orderOf σ = 3 := by
  have h3 : IsThreeCycle (swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ *
      swap (⟨0, by omega⟩ : Fin m) ⟨2, by omega⟩) :=
    isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  exact ⟨⟨_, h3.mem_alternatingGroup⟩, by rw [Subgroup.orderOf_mk]; exact h3.orderOf⟩

theorem le_thetaOf_of_isChi0Block [Finite G] {X L : Subgroup G} (hL : IsChi0Block X L) :
    L ≤ thetaOf L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hshort, -, -⟩, hty⟩ := hL
  have halt : ∀ m, 3 ≤ m → IsSimpleGroup (alternatingGroup (Fin m)) → IsAltType L m →
      L ≤ thetaOf L := by
    intro m hm hsimp hA
    obtain ⟨α, hαs, hαk, -⟩ := hA
    obtain ⟨σ, hσ⟩ := exists_orderOf_three_alternating hm
    obtain ⟨y, hy⟩ := hαs σ
    have h3 : 3 ∣ Nat.card ↥L := by
      rw [← hσ, ← hy]
      exact (orderOf_map_dvd α y).trans (orderOf_dvd_natCard y)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    exact le_thetaOf_of_simple_quotient hshort.1 α hαs hαk z.2
      (by rw [Subgroup.orderOf_coe]; exact hz)
  rcases hty with ⟨n, hn, hlin⟩ | h3 | h5
  · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (AppE.three_dvd_card_lin2 hlin)
    obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := hlin
    have := AppE.sl2_isSimpleGroup (by omega) hcard
    exact le_thetaOf_of_simple_quotient hshort.1 α hαs hαk z.2
      (by rw [Subgroup.orderOf_coe]; exact hz)
  · refine halt 3 le_rfl (isSimpleGroup_of_prime_card (p := 3) ?_) h3
    rw [Lem8.card_alternatingGroup_fin (by norm_num)]
    decide
  · exact halt 5 (by norm_num) (alternatingGroup.isSimpleGroup (by rw [Nat.card_fin])) h5

end Theta

theorem A6quot_facts {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hodd : Odd (Nat.card (center X))) (e : X ⧸ center X ≃* alternatingGroup (Fin 6)) :
    (Nat.card (center X) = 1 ∨ Nat.card (center X) = 3) ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  by_cases hZ : center X = ⊥
  · refine ⟨Or.inl (by rw [hZ, card_bot]), ?_⟩
    set e' : X ≃* alternatingGroup (Fin 6) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans e
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e']
    exact Rank8.two_le_pRank_alternating_six
  · set π : X →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
      with hπ
    have hker : π.ker = center X := by
      ext g
      simp [hπ]
    have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    obtain ⟨h3, -⟩ := A7_alternating_six_seven_odd_cover_cubic_Sylow (n := 6) (Or.inl rfl) π hπs
      (hker.le) (by rw [hker]; exact hodd) (by rw [hker]; exact hZ)
    rw [hker] at h3
    exact ⟨Or.inr h3, Rank8.two_le_pRank_of_isHatAlt (Or.inl rfl) h3 e⟩

variable {G : Type} [Group G] [Finite G]

theorem thetaOf_le_of_A6
    (hF : A318Facts) (h38 : A38ForSQTK)
    (hqtke : QuasithinUnique.quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {H K : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥)
    (hK : K ∈ cComp H) (hKn : (K.subgroupOf H).Normal)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hA6 : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      alternatingGroup (Fin 6))) :
    thetaOf H ≤ K := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e6⟩ := hA6
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hsqtk : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hqtke hs hnab hH
  have hhyp := sqtkHyp_quotient_of_pCoreOf_ne_bot hqtke hs hnab hH
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  have hcomp : K' ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hK
  let eL : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  let eQ : ↥K' ⧸ CFSG.pCore 2 ↥K' ≃* ↥K ⧸ CFSG.pCore 2 ↥K :=
    QuotientGroup.congr _ _ eL (CFSG.pCore_map_iso 2 eL)
  have hQ' : CFSG.IsQuasisimple (↥K' ⧸ CFSG.pCore 2 ↥K') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm hKq
  obtain ⟨hperf, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hKq
  obtain ⟨hZ13, hR⟩ := A6quot_facts hodd e6
  have h2K : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := ↥K) (p := 2))
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hrank : 1 < CFSG.Open.pRank 3 K' := by
    rw [← pRank_top_subtype K', CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eL,
      ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K) h2K]
    omega
  have hZQ : Nat.card (center (↥K' ⧸ CFSG.pCore 2 ↥K')) ∣ 3 := by
    rw [Lem8.card_center_eq_of_mulEquiv eQ]
    rcases hZ13 with h | h <;> rw [h]
    exact one_dvd 3
  obtain ⟨g3, hg3⟩ := Lem8.exists_orderOf_eq_three_of_two_le_pRank (le_trans (by norm_num) hR)
  have : K'.Normal := hKn
  obtain ⟨eS⟩ := Lem8.nonempty_mulEquiv_starImage K' hQ' hZQ
    ⟨eQ.symm g3, by rw [MulEquiv.orderOf_eq]; exact hg3⟩
  let e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(starImage 3 K') := eQ.symm.trans eS
  have hcardX : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) =
      360 * Nat.card (center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    rw [card_eq_card_quotient_mul_card_subgroup (center _), Nat.card_congr e6.toEquiv,
      Lem8.card_alternatingGroup_fin (by norm_num)]
    rfl
  have hcardS : Nat.card ↥(starImage 3 K') = 360 ∨ Nat.card ↥(starImage 3 K') = 1080 := by
    rw [← Nat.card_congr e.toEquiv, hcardX]
    rcases hZ13 with h | h <;> rw [h] <;> norm_num
  have hX : L34.ListOrd (Nat.card ↥(starImage 3 K')) := by
    unfold L34.ListOrd
    omega
  have hX8 : Nat.card ↥(starImage 3 K') = 20160 →
      Nonempty (↥(starImage 3 K') ≃* alternatingGroup (Fin 8)) := fun h => by
    exfalso
    omega
  have hXhat : Nat.card (center ↥(starImage 3 K')) = 3 →
      Nat.card ↥(starImage 3 K') = 1080 ∨ Nat.card ↥(starImage 3 K') = 7560 := fun h => by
    left
    rw [← Lem8.card_center_eq_of_mulEquiv e] at h
    rw [← Nat.card_congr e.toEquiv, hcardX, h]
  rcases a318 hF hsqtk (VolI.a36ForSQTK_holds _ hhyp) (h38 _ hhyp) hcomp hQ' Nat.prime_three
      (by norm_num) hrank with h1 | ⟨-, s, q, hq, hpsl, -⟩ | ⟨-, h3g, h3⟩
  ·
    have hK1 := Lem8.eq_closure_image_of_subgroupOf_eq hKH h1
    rw [Lem8.image_pElements_three] at hK1
    rw [hK1]
    refine closure_mono ?_
    rintro x ⟨hx, hx3⟩
    exact ⟨hx, 1, by rw [pow_one, ← hx3]; exact pow_orderOf_eq_one x⟩
  · exact (L34.not_isPSLEps3q_of_card hX hX8 s q hq hpsl).elim
  · have hZ3 : Nat.card (center ↥(starImage 3 K')) = 3 := by
      rcases h3g with ⟨s, q, hq, hsl⟩ | hA | hA | hM22
      · exact (L34.not_isSLEps3_of_card hX s q hq hsl).elim
      · exact hA.2.1
      · exact hA.2.1
      · exact (Lem8.not_isHat_M22 hX hM22).elim
    rcases h3 with hθ | ⟨s, q, x, hsl, -⟩
    · have hK1 := Lem8.eq_closure_image_of_subgroupOf_eq hKH hθ
      rw [Lem8.image_orderThree] at hK1
      rw [hK1]
      rfl
    · exact (L34.not_isSLEps3_of_card_hat (hXhat hZ3) s q hsl).elim

end CFSG.Quasithin.H13.A7
