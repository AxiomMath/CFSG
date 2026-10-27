module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNH
public import CFSG.Quasithin.Background.C2Seven
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNC
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

theorem c27_caseH (h331 : Stmt3_3_1) (hC27 : ASC27Statement G) (hG2 : Lem1211NNG2)
    (hSL3 : Lem1211NNSL3) (F : Frame S m) (hm : 3 ≤ m)
    (hchar : CharTwo (Subgroup.centralizer ({a₀ * c₀} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hlt : Sec1216Lv.lv L (a₀ * c₀) < K)
    (hKn : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {Q Mv U : Subgroup G}
    (hQ : Q = T ⊓ Subgroup.centralizer (V : Set G))
    (hMv : Mv = Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G))
    (hU : U = omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) :
    (pCoreOf 2 (K ⊔ Q) ≤ (K ⊔ Q) ⊓ Subgroup.centralizer (U : Set G) ∧
        (K ⊔ Q) ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 (K ⊔ Q) ⊔ oTwoZIn K ∧
        IsTwoReducedIn (K ⊔ Q) U) ∧
      (∃ hUe : IsElemAbelian 2 U, ∃ A : Subgroup (MulAut ↥U), A ≤ autOn Q U ∧
        @IsFFStarOffender U (commGroupOfElemAbelian hUe) (autOn (K ⊔ Q) U) A) ∧
      (Nonempty (↥(autOn K U) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) ∨
          Nonempty (↥(autOn K U) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)))) ∧
        IsParabolic2 (autOn K U) (autOn (Mv ⊓ K) U) ∧ ¬ IsBorelIn (autOn K U) (autOn (Mv ⊓ K) U) := by
  subst hQ hMv hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hHdef
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLvdef
  set Mv := M ⊓ H with hMvdef
  set U := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hUdef
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hCV : Subgroup.centralizer (V : Set G) ≤ H :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.v_mem)
  have hQMv : Q ≤ Mv := le_inf (inf_le_left.trans S.hTL) (inf_le_right.trans hCV)
  obtain ⟨R, hR, hQR⟩ := A4.exists_isSylowTwoOf_ge hQMv hQ2
  have hyp0 := S.hypC23_of_le h331 F hm le_rfl (Sec1216Lv.lv_le_centralizer L _) hR
    (hR.1.trans inf_le_right) hQR
  have hyp : HypC23 H Q Mv := by
    have e : M ⊓ H ⊓ H = Mv := by rw [inf_assoc, inf_idem]
    rwa [e] at hyp0
  have hKc : CharTwo K := A4.charTwo_of_normal hKH hKn hchar
  have hKM : ¬ K ≤ Mv := fun h =>
    S.not_le_normalizer_L_of_lt F (by omega) hK hlt (h.trans inf_le_left)
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := (inf_le_right.trans hCV).trans hKn
  obtain ⟨h1, ⟨-, hUe, -, A, hAQ, hA⟩, h3⟩ := hC27 H Q Mv K U hyp hK hq hKc hKM hQK rfl
  refine ⟨h1, ⟨hUe, A, hAQ, hA⟩, ?_⟩
  have hXU : K ⊔ Q ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    A4.normalizer_le_normalizer_omegaOneCenterOf _
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ Q) hg)
  have hLvK : Lv ≤ K := hlt.le
  have hLvU : Lv ≤ Subgroup.normalizer (U : Set G) := hLvK.trans (le_sup_left.trans hXU)
  have hLvMv : Lv ≤ Mv :=
    le_inf ((Sec1216Lv.lv_le_L L _).trans Subgroup.le_normalizer) (Sec1216Lv.lv_le_centralizer L _)
  have hWU : S.W₁ ⊔ S.W₂ ≤ U :=
    (sup_le (S.W₁_le.trans S.le₁) (S.W₂_le.trans S.le₂)).trans
      (S.le_omegaOneCenterOf h331 F hm hchar hKH hKn)
  obtain ⟨π, hπs, hπk, -⟩ := S.exists_pi_autOn F hWU hLvU
  have hD7 : 7 ∣ Nat.card ↥(autOn Lv U) := Sec1211Nq.seven_dvd_card_of_surjective hm π hπs
  have hDperf : ⁅autOn Lv U, autOn Lv U⁆ = autOn Lv U :=
    Sec1211Nq.autOn_perfect (Sec1216Lv.lv_perfect L _) hLvU
  have hDP : autOn Lv U ≤ autOn (Mv ⊓ K) U := A4.autOn_mono (le_inf hLvMv hLvK)
  have hDX : autOn Lv U ≤ autOn (K ⊔ Q) U := A4.autOn_mono (hLvK.trans le_sup_left)
  have hLv7 : 7 ∣ Nat.card ↥Lv := S.seven_dvd_card_lv F hm
  have hMK7 : 7 ∣ Nat.card ↥(Mv ⊓ K) :=
    hLv7.trans (Subgroup.card_dvd_of_le (le_inf hLvMv hLvK))
  have hq7 : 7 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Sec1211Nq.seven_dvd_card_quot (hLv7.trans (Subgroup.card_dvd_of_le hLvK))
  have hm4 : m = 3 ∨ m = 4 := by
    have := F.h
    rcases S.hyp.rank with h | h <;> omega
  rcases h3 with ⟨-, ⟨-, -, hB⟩ | ⟨-, -, -, hB⟩ | ⟨-, -, e, P, hP, hmap⟩ | ⟨-, -, e, P, hP, hmap⟩⟩ |
      ⟨⟨r, α, hr5, hr8, -, hwith, t₀, ht₀Q, ht₀U, hzp, -, σ, hσ, hσc⟩, hMK⟩ |
      ⟨⟨-, hhat, -⟩, -⟩ | ⟨⟨-, ⟨α, hαs, hαk⟩, -⟩, hidx⟩ |
      ⟨⟨-, α, hwith6⟩ | ⟨-, F', _, _, hF4, α, hαs, hαk, -⟩, -⟩ |
      ⟨-, hG2two, hmaxp⟩ | ⟨⟨k, F', _, _, hk1, hFc, ⟨e⟩⟩, hmaxp, -⟩ | h
  ·
    have := Sec1211Nq.isSolvable_of_isBorelIn hB
    exact (Sec1211Nq.false_of_perfect_le_solvable hDperf hDP hD7).elim
  ·
    have := Sec1211Nq.isSolvable_of_isBorelIn hB
    exact (Sec1211Nq.false_of_perfect_le_solvable hDperf hDP hD7).elim
  ·
    obtain ⟨x, hxD, hx7⟩ := Sec1211Nq.exists_orderOf_seven hD7
    exact (Sec1211Nq.false_of_map_eq_stabilizer e hP (by simp) (by simp) hmap (hDP hxD)
      (hDX hxD) hx7).elim
  ·
    obtain ⟨x, hxD, hx7⟩ := Sec1211Nq.exists_orderOf_seven hD7
    exact (Sec1211Nq.false_of_map_eq_stabilizer e hP (by simp) (by simp) hmap (hDP hxD)
      (hDX hxD) hx7).elim
  ·
    obtain ⟨x, hxD, hx7⟩ := Sec1211Nq.exists_orderOf_seven hD7
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hxD
    have hgLv : (g : G) ∈ Lv := Subgroup.mem_subgroupOf.mp hg
    have hxC : conjAct U g ∈ Subgroup.centralizer (autOn Q U : Set (MulAut ↥U)) := by
      have h1 := hDP hxD
      rw [hMK] at h1
      exact h1.2
    have hc : conjAct U ⟨t₀, ht₀U⟩ ∈ autOn Q U := by
      rw [hzp]
      exact Subgroup.mem_zpowers _
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC _ hc
    exact (Sec1211Nq.false_of_caseB hQK h1.2.1 hr5 hr8 α hwith.1 hwith.2.1 ht₀Q ht₀U hσ hσc
      (hLvK hgLv) g.2 hx7 hcomm.symm).elim
  ·
    obtain ⟨-, hc3, ⟨eA⟩⟩ := hhat
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))
    rw [hc3, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h1
    rw [h1] at hq7
    norm_num [Nat.factorial] at hq7
  ·
    have hq' : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 := by
      rw [Sec1211Nq.card_quot_eq_of_surjective α hαs hαk, nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact (Sec1211Nq.false_of_relIndex_thirtyFive hq' hidx hMK7).elim
  ·
    rw [Sec1211Nq.card_quot_eq_of_surjective α hwith6.1 hwith6.2.1, nat_card_alternatingGroup,
      Nat.card_fin] at hq7
    norm_num [Nat.factorial] at hq7
  ·
    rw [Sec1211Nq.card_quot_eq_of_surjective α hαs hαk,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_eq_fintype_card,
      hF4] at hq7
    exact absurd hq7 (by decide)
  ·
    exact (hG2 _ _ _ hG2two hmaxp (hD7.trans (Subgroup.card_dvd_of_le (hDP.trans le_sup_left)))).elim
  ·
    exact (hSL3 _ _ _ _ F' k m hk1 hFc ⟨e⟩ hmaxp hDP hm4 π hπs hπk).elim
  ·
    exact h

omit [Finite G] in
theorem autOn_le_normalizer_autOn {A B U : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    autOn A U ≤ Subgroup.normalizer (autOn B U : Set (MulAut ↥U)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hAB

theorem swap_not_inner_autOn (F : Frame S m) (hm : 3 ≤ m) {U : Subgroup G}
    (hLvU : Sec1216Lv.lv L (a₀ * c₀) ≤ Subgroup.normalizer (U : Set G))
    (π : ↥(autOn (Sec1216Lv.lv L (a₀ * c₀)) U) →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (hπ : ∀ l, π (InternalSec.autOnHom hLvU l) = psi F S.lv_le_Xv l) {t : G}
    (htM : t ∈ Subgroup.normalizer (L : Set G)) (hta : t * a₀ * t⁻¹ = c₀)
    (htc : t * c₀ * t⁻¹ = a₀) (htU : t ∈ Subgroup.normalizer (U : Set G))
    (htLv : t ∈ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G))
    (hτD : conjAct U ⟨t, htU⟩ ∈
      Subgroup.normalizer (autOn (Sec1216Lv.lv L (a₀ * c₀)) U : Set (MulAut ↥U))) :
    ¬ ∃ z : Matrix.SpecialLinearGroup (Fin m) (ZMod 2),
      ∀ d : ↥(autOn (Sec1216Lv.lv L (a₀ * c₀)) U),
        π ⟨conjAct U ⟨t, htU⟩ * d * (conjAct U ⟨t, htU⟩)⁻¹,
          (Subgroup.mem_normalizer_iff.mp hτD d).mp d.2⟩ = z * π d * z⁻¹ := by
  rintro ⟨z, hz⟩
  apply S.swap_not_inner F hm htM hta htc htLv
  refine ⟨z, fun x => ?_⟩
  have hx' : t * (x : G) * t⁻¹ ∈ Sec1216Lv.lv L (a₀ * c₀) :=
    (Subgroup.mem_normalizer_iff.mp htLv x).mp x.2
  have e : (⟨conjAct U ⟨t, htU⟩ * (InternalSec.autOnHom hLvU x : MulAut ↥U) *
      (conjAct U ⟨t, htU⟩)⁻¹, (Subgroup.mem_normalizer_iff.mp hτD _).mp
        (InternalSec.autOnHom hLvU x).2⟩ : ↥(autOn (Sec1216Lv.lv L (a₀ * c₀)) U)) =
      InternalSec.autOnHom hLvU ⟨t * x * t⁻¹, hx'⟩ := by
    apply Subtype.ext
    show conjAct U ⟨t, htU⟩ * conjAct U ⟨x, hLvU x.2⟩ * (conjAct U ⟨t, htU⟩)⁻¹ =
      conjAct U ⟨t * x * t⁻¹, hLvU hx'⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have h1 := hz (InternalSec.autOnHom hLvU x)
  rw [e, hπ, hπ] at h1
  exact h1

theorem caseH_of_c27 (h331 : Stmt3_3_1) (hC27 : ASC27Statement G) (hParab : Lem1211NNParab)
    (hG2 : Lem1211NNG2) (hSL3 : Lem1211NNSL3) (F : Frame S m) (hm : 3 ≤ m)
    (hchar : CharTwo (Subgroup.centralizer ({a₀ * c₀} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hlt : Sec1216Lv.lv L (a₀ * c₀) < K)
    (hKn : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {t : G}
    (htM : t ∈ Subgroup.normalizer (L : Set G)) (hta : t * a₀ * t⁻¹ = c₀)
    (htc : t * c₀ * t⁻¹ = a₀)
    (htQ : t ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) :
    m = 3 ∧
      Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))))))
        ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) ∧
      ∃ htU : t ∈ Subgroup.normalizer
          ((omegaOneCenterOf (pCoreOf 2 (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))))) : Set G),
        ¬ ∃ x ∈ autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))))),
          ∀ y ∈ autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))))),
            conjAct _ ⟨t, htU⟩ * y * (conjAct _ ⟨t, htU⟩)⁻¹ = x * y * x⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLvdef
  set Mv := Subgroup.normalizer (L : Set G) ⊓ H with hMvdef
  set U := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hUdef
  obtain ⟨⟨-, hC1, -⟩, -, hiso, hpar, hnotB⟩ :=
    S.c27_caseH h331 hC27 hG2 hSL3 F hm hchar hK hlt hKn hq hQdef hMvdef hUdef
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hCV : Subgroup.centralizer (V : Set G) ≤ H :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.v_mem)
  have hXU : K ⊔ Q ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    A4.normalizer_le_normalizer_omegaOneCenterOf _
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ Q) hg)
  have hLvK : Lv ≤ K := hlt.le
  have hLvU : Lv ≤ Subgroup.normalizer (U : Set G) := hLvK.trans (le_sup_left.trans hXU)
  have hLvMv : Lv ≤ Mv :=
    le_inf ((Sec1216Lv.lv_le_L L _).trans Subgroup.le_normalizer) (Sec1216Lv.lv_le_centralizer L _)
  have hWU : S.W₁ ⊔ S.W₂ ≤ U :=
    (sup_le (S.W₁_le.trans S.le₁) (S.W₂_le.trans S.le₂)).trans
      (S.le_omegaOneCenterOf h331 F hm hchar hKH hKn)
  obtain ⟨π, hπs, hπk, hπ⟩ := S.exists_pi_autOn F hWU hLvU
  have hDP : autOn Lv U ≤ autOn (Mv ⊓ K) U := A4.autOn_mono (le_inf hLvMv hLvK)
  have hm4 : m = 3 ∨ m = 4 := by
    have := F.h
    rcases S.hyp.rank with h | h <;> omega
  have htH : t ∈ H := S.mem_centralizer_of_swap hta htc
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hKn htH
  have htU : t ∈ Subgroup.normalizer (U : Set G) :=
    A4.normalizer_le_normalizer_omegaOneCenterOf _
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (mem_normalizer_sup htK htQ))
  have hMvLv : Mv ≤ Subgroup.normalizer (Lv : Set G) :=
    Sec1216Lv.le_normalizer_lv inf_le_left inf_le_right
  have htMv : t ∈ Mv := ⟨htM, htH⟩
  have htLv : t ∈ Subgroup.normalizer (Lv : Set G) := hMvLv htMv
  have hτX := conjAct_mem_normalizer_autOn ⟨t, htU⟩ htK
  have hτP := conjAct_mem_normalizer_autOn ⟨t, htU⟩
    (Sec1216Gen.mem_normalizer_inf (Subgroup.le_normalizer htMv) htK)
  have hτD := conjAct_mem_normalizer_autOn ⟨t, htU⟩ htLv
  have hPD : autOn (Mv ⊓ K) U ≤ Subgroup.normalizer (autOn Lv U : Set (MulAut ↥U)) :=
    autOn_le_normalizer_autOn (inf_le_left.trans hMvLv)
  have hout := S.swap_not_inner_autOn F hm hLvU π hπ htM hta htc htU htLv hτD
  rcases hiso with he4 | he5
  · rcases hParab _ (autOn K U) (autOn (Mv ⊓ K) U) (autOn Lv U) 4 m (conjAct U ⟨t, htU⟩)
        (Or.inl rfl) hm4 he4 hpar hnotB hDP hPD π hπs hπk hτX hτP hτD hout with
      ⟨h, -⟩ | ⟨-, -, hPX⟩
    · exact absurd h (by norm_num)
    · exact (S.false_of_autOn_eq h331 F hm hK hlt hKn hq hXU hC1 hPX).elim
  · rcases hParab _ (autOn K U) (autOn (Mv ⊓ K) U) (autOn Lv U) 5 m (conjAct U ⟨t, htU⟩)
        (Or.inr rfl) hm4 he5 hpar hnotB hDP hPD π hπs hπk hτX hτP hτD hout with
      ⟨-, hm3, hτ⟩ | ⟨h, -⟩
    · exact ⟨hm3, he5, htU, hτ⟩
    · exact absurd h (by norm_num)

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
