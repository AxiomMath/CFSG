module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25C
public import CFSG.Quasithin.Vol2.Ch12Sec5L11
public import CFSG.Quasithin.H13.A7KLocal
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20
public import CFSG.Quasithin.Background.I62Pair
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

namespace Lem25

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_centralizer {U K : Subgroup G}
    (hKU : K ≤ Subgroup.centralizer (U : Set G)) {x : G} (hx : x ∈ U ⊔ K) :
    ∃ u ∈ U, ∃ k ∈ K, u * k = x :=
  Lem24.exists_mul_of_mem_sup_normal (hKU.trans (Subgroup.centralizer_le_normalizer _)) hx

theorem card_sup_eq_mul [Finite G] {U K : Subgroup G} (hKU : K ≤ Subgroup.centralizer (U : Set G))
    (hUK : U ⊓ K = ⊥) : Nat.card ↥(U ⊔ K) = Nat.card U * Nat.card K := by
  let f : ↥U × ↥K → ↥(U ⊔ K) := fun x =>
    ⟨(x.1 : G) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
      have h2 : (y.1 : G)⁻¹ * x.1 ∈ U ⊓ K := by
        refine ⟨U.mul_mem (U.inv_mem y.1.2) x.1.2, ?_⟩
        rw [show (y.1 : G)⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ by
          calc (y.1 : G)⁻¹ * x.1 = (y.1 : G)⁻¹ * (x.1 * x.2) * (x.2 : G)⁻¹ := by group
            _ = (y.1 : G)⁻¹ * (y.1 * y.2) * (x.2 : G)⁻¹ := by rw [h1]
            _ = y.2 * (x.2 : G)⁻¹ := by group]
        exact K.mul_mem y.2.2 (K.inv_mem x.2.2)
      rw [hUK, Subgroup.mem_bot] at h2
      have h3 : (x.1 : G) = y.1 := by
        have := congrArg ((y.1 : G) * ·) h2
        simpa using this
      have h4 : (x.2 : G) = y.2 := by
        rw [h3] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
    · obtain ⟨u, hu, k, hk, hz⟩ := exists_mul_of_mem_sup_centralizer hKU z.2
      exact ⟨(⟨u, hu⟩, ⟨k, hk⟩), Subtype.ext hz⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end Lem25

open Lem25

theorem lem12225Star_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) :
    ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
      Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p →
        T ⊓ Subgroup.centralizer (U : Set G) = U ⊔ (T ⊓ Subgroup.centralizer (I : Set G)) ∧
        U ⊓ Subgroup.centralizer (I : Set G) = ⊥ ∧
        T ⊓ Subgroup.centralizer (U : Set G) = U ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
        U ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
        V ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        T ⊓ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer (I : Set G) = ⊥ ∧
        IsElemAbelian 2 (T ⊓ Subgroup.centralizer (U : Set G)) ∧
        Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 ∧
        T = (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
        quasithinOmegaOneCenter T =
          (V ⊓ Subgroup.centralizer (T : Set G)) ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
        Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) = 2 ∧
        oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) ⊔ T ≤
          Subgroup.normalizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
  intro G _ _ T L V H P U I h n p hH hNE hC
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨hHs, -, hn, hVn, hTLC, -, hp, hp2, hP, hord, hhH, hhM, hI, hU, hUd, hUi, hUe, hD, hUP,
    hidx, ⟨hcommV, htv⟩, hUO, -, hK, hHU, hHI, hIP, -, hIM, hQU⟩ := hC
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set Q := pCoreOf 2 (L ⊔ (S : Subgroup G)) with hQdef
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hredV, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hTI := h1216 G S L V hH hNE
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have hTH : (S : Subgroup G) ≤ H := hHs.1.1
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  have hVQ : ∀ v ∈ V, v ∈ Q ∧ ∀ k ∈ Q, k * v = v * k := fun v hv =>
    ⟨(S125.mem_R2 (hH.irrPlus.1 hv)).1, (S125.mem_R2 (hH.irrPlus.1 hv)).2.1⟩
  have hNVM : Subgroup.normalizer (V : Set G) ≤ M :=
    Lem20.normalizer_le_of_hyp1223 (stmt12_2_6_of h1222 h323) hH
  have hPh : (P : Subgroup G) = Subgroup.zpowers h := hP
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hHU hhH
  have hUle : U ≤ I := by rw [hIP]; exact le_sup_right.trans le_sup_left
  have hPI : P ≤ I := by rw [hIP]; exact le_sup_left.trans le_sup_left
  have hVI : V ≤ I := by rw [hIP]; exact le_sup_right
  have hUC : U ≤ Subgroup.centralizer (U : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => hUab w hw u hu
  have hU1 : U ≠ ⊥ := by
    intro hU0
    rw [hU0, bot_inf_eq, Subgroup.relIndex_bot_left, hVn] at hidx
    rcases hn with rfl | rfl | rfl <;> norm_num at hidx
  have hVP : V ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, hvP⟩
    have hc := Subgroup.mem_centralizer_iff.mp hvP h (hPh ▸ Subgroup.mem_zpowers h)
    rcases hTI h with h1 | h1
    · exfalso
      apply hhM
      refine hNVM (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
      rw [← BlueprintB2.mem_conjugate_iff, h1]
    · have : v ∈ V ⊓ CFSG.conjugate V h := ⟨hv, BlueprintB2.mem_conjugate_iff.mpr (by
        rw [show h * v * h⁻¹ = v by rw [hc]; group]
        exact hv)⟩
      rw [h1] at this
      exact this
  have hc1 : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) =
      U ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (I : Set G)) := by
    apply le_antisymm
    · rintro x ⟨hxS, hxU⟩
      have hxh : x * h * x⁻¹ ∈ U ⊔ Subgroup.zpowers h := by
        have h1 : h ∈ oTwoUpper H := by
          rw [hK, hPh]
          exact Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
        have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH hxS)) h).mp h1
        rwa [hK, hPh, sup_comm] at h2
      obtain ⟨u, hu, hc⟩ :=
        exists_mem_centralizer_of_conj hp hord hUab hhU (hPh ▸ hUP) hU1 hxU hxh
      have hcS : u⁻¹ * x ∈ (S : Subgroup G) := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUT hu)) hxS
      have hcU : u⁻¹ * x ∈ Subgroup.centralizer (U : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUC hu)) hxU
      have hcP : u⁻¹ * x ∈ Subgroup.centralizer (P : Set G) := hPh ▸ hc
      have hcPU := mem_centralizer_sup hcP hcU
      have hcV : u⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hvN : v ∈ Subgroup.normalizer ((P ⊔ U : Subgroup G) : Set G) := by
          rw [← hK]
          exact le_normalizer_oTwoUpper H (hTH (hVT hv))
        have hvC := B6.le_normalizer_centralizer le_rfl hvN
        have hw1 : u⁻¹ * x * v * (u⁻¹ * x)⁻¹ * v⁻¹ ∈ V :=
          V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTV hcS) v).mp hv) (V.inv_mem hv)
        have hw2 : u⁻¹ * x * v * (u⁻¹ * x)⁻¹ * v⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
          have h3 : v * (u⁻¹ * x)⁻¹ * v⁻¹ ∈
              Subgroup.centralizer ((P ⊔ U : Subgroup G) : Set G) :=
            (Subgroup.mem_normalizer_iff.mp hvC _).mp (Subgroup.inv_mem _ hcPU)
          have h4 := Subgroup.mul_mem _ hcPU h3
          rw [show u⁻¹ * x * (v * (u⁻¹ * x)⁻¹ * v⁻¹) = u⁻¹ * x * v * (u⁻¹ * x)⁻¹ * v⁻¹ by
            group] at h4
          exact Subgroup.centralizer_le (le_sup_left : P ≤ P ⊔ U) h4
        have h5 : u⁻¹ * x * v * (u⁻¹ * x)⁻¹ * v⁻¹ ∈ V ⊓ Subgroup.centralizer (P : Set G) :=
          ⟨hw1, hw2⟩
        rw [hVP, Subgroup.mem_bot] at h5
        calc v * (u⁻¹ * x) = (u⁻¹ * x * v * (u⁻¹ * x)⁻¹ * v⁻¹)⁻¹ * (u⁻¹ * x) * v := by group
          _ = u⁻¹ * x * v := by rw [h5, inv_one, one_mul]
      have hcI : u⁻¹ * x ∈ Subgroup.centralizer (I : Set G) := by
        rw [hIP]
        exact mem_centralizer_sup hcPU hcV
      rw [show x = u * (u⁻¹ * x) by group]
      exact Subgroup.mul_mem_sup hu ⟨hcS, hcI⟩
    · exact sup_le (le_inf hUT hUC) (inf_le_inf_left _ (Subgroup.centralizer_le hUle))
  have hc1b : U ⊓ Subgroup.centralizer (I : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hUP]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hPI)
  have hc4 : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer (I : Set G) = ⊥ := by
    by_contra hne
    set T₀ := (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer (I : Set G) with hT₀
    have hT₀2 : IsPGroup 2 T₀ := S.isPGroup'.to_le (inf_le_left.trans inf_le_left)
    have hloc : IsTwoLocal (Subgroup.normalizer (T₀ : Set G)) := ⟨T₀, hne, hT₀2, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hLN : L ≤ Subgroup.normalizer (T₀ : Set G) :=
      (Subgroup.le_centralizer_iff.mp (inf_le_left.trans inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hTN : (S : Subgroup G) ≤ Subgroup.normalizer (T₀ : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer ht, B6.le_normalizer_centralizer hH.normalizes ht⟩,
          B6.le_normalizer_centralizer hHI (hTH ht)⟩
    have hIN : I ≤ Subgroup.normalizer (T₀ : Set G) :=
      (Subgroup.le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
    have heq := ((h331 G S hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal
      hH.quasisimple).1.2.2 M' hM' ((sup_le hLN hTN).trans hle)
    rw [hH.conjClosure_eq] at heq
    exact hIM (hIN.trans (hle.trans heq.le))
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl | rfl <;> norm_num
  obtain ⟨e⟩ := Lem24.nonempty_coords (V := V) hVab (fun v hv => hVe.2 v hv) hVn
  have hCV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    Lem24.inf_centralizer_eq_bot hLV (by omega) e htop
  have : IsMulCommutative ↥V := hcommV
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact Subtype.ext (hVe.2 v v.2)
  have hQU' : ∀ q ∈ Q, ∀ u ∈ U, ⁅q, u⁆ ∈ V := fun q hq u hu =>
    (hQU (Subgroup.commutator_mem_commutator hq hu)).2
  have hUVaut : autOn U V ≠ ⊥ := by
    rw [htv]
    have hA2 : ((U ⊓ V).subgroupOf V).index = 2 := hidx
    obtain ⟨a, ha, ha1⟩ : ∃ a ∈ (U ⊓ V).subgroupOf V, a ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : (U ⊓ V).subgroupOf V = ⊥ := eq_bot_iff.mpr fun a ha =>
        Subgroup.mem_bot.mpr (hno a ha)
      rw [hbot, Subgroup.index_bot] at hA2
      rw [hA2] at hVn
      rcases hn with rfl | rfl | rfl <;> norm_num at hVn
    exact Lem24.transvAxis_ne_bot (fun w => (by rw [pow_two]; exact hV2' w)) hA2 ha ha1
  have hQV : ∀ q ∈ Q, ∀ l ∈ L, ⁅q, l⁆ ∈ V :=
    Lem24.commutator_mem_of_mem_pCoreOf hH hTV hredV hn3 e htop hUT hQU' hUVaut
  have hbU : blockU L = V := Lem24.blockU_eq hH hVT hTV hredV hn3 e htop hUT hQU' hUVaut
  have hCLV' : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L :=
    Lem24.centralizer_le_pCoreOf hH hredV hn3 e htop
  have hQT : Q ≤ (S : Subgroup G) := A7.pCoreOf_le_of_le_normalizer S
    (le_sup_right.trans Subgroup.le_normalizer)
  have hqL : ∀ q ∈ Q, ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ V := fun q hq l hl => by
    have := hQV q hq l hl
    rwa [commutatorElement_def] at this
  have hqC : ∀ q ∈ Q, ∀ l ∈ L, l ∈ Subgroup.centralizer (V : Set G) →
      q * l * q⁻¹ * l⁻¹ = 1 := fun q hq l hl hlV =>
    comm_eq_one_of_mem_pCoreOf hLV hVab hbU hCV (fun v hv => (hVQ v hv).2 q hq) (hqL q hq)
      (hCLV' ⟨hl, hlV⟩) hlV
  have hVL : V ≤ L := by
    rw [← commutator_eq_of_hyp1223 hH, Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hH.normalizes (hVT hv)) l).mp hl)
      (L.inv_mem hl)
  have hCLV : Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le hVL
  have hCVQ' : (L ⊔ (S : Subgroup G)) ⊓ Subgroup.centralizer (V : Set G) ≤ Q := by
    set X := (L ⊔ (S : Subgroup G)) ⊓ Subgroup.centralizer (V : Set G) with hX
    have hX2 : IsPGroup 2 X := by
      intro ⟨x, hx⟩
      obtain ⟨l, hl, t, ht, hlt⟩ := Lem24.exists_mul_of_mem_sup_normal hH.normalizes hx.1
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨t, ht⟩
      have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨z, hz, hzt⟩ := Lem24.exists_pow_eq_mul_pow hl (hH.normalizes ht) (2 ^ k)
      rw [hk', mul_one] at hzt
      have hzV : z ∈ Subgroup.centralizer (V : Set G) := by
        rw [← hzt, hlt]
        exact Subgroup.pow_mem _ hx.2 _
      have hzO := hCLV' ⟨hz, hzV⟩
      obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨z, hzO⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have hj' : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      show (x : G) ^ 2 ^ (k + j) = 1
      rw [pow_add, pow_mul, ← hlt, hzt, hj']
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        B6.le_normalizer_centralizer (sup_le hLV hTV) hg⟩) hX2
  have hCVQ : (S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ≤ Q := fun x hx =>
    hCVQ' ⟨Subgroup.mem_sup_right hx.1, hx.2⟩
  set A := CFSG.conjugate V h with hAdef
  have hVA : V ⊓ A = ⊥ := by
    rcases hTI h with h1 | h1
    · exfalso
      apply hhM
      refine hNVM (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
      rw [← BlueprintB2.mem_conjugate_iff, h1]
    · exact h1
  have hBase : I62.Base V A := ⟨hVe, isElemAbelian_conjugate' hVe h,
    conjugate_one V ▸ isTISetIn_conjugate hTI 1, isTISetIn_conjugate hTI h, hVA⟩
  have hUN : U ≤ Subgroup.normalizer (V : Set G) := hUT.trans hTV
  have htiU : ASInputs.tiU V A ≠ V := by
    intro htU
    have hVNA : V ≤ Subgroup.normalizer (A : Set G) := htU ▸ inf_le_right
    have hI2 : IsPGroup 2 I := by
      rw [hI]
      exact IsPGroup.to_sup_of_normal_right' (B2F.isPGroup_of_isElemAbelian hVe)
        (B2F.isPGroup_of_isElemAbelian (isElemAbelian_conjugate' hVe h)) hVNA
    obtain ⟨_, ⟨eD⟩⟩ := hD
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf I)
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card] at hcard
    obtain ⟨k, hk⟩ := hI2.exists_card_eq
    have hpd : p ∣ 2 ^ k := by
      rw [← hk, hcard]
      exact Dvd.dvd.mul_right (dvd_mul_left p 2) _
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd))
  have hCUV : U ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    rintro u ⟨hu, huV⟩
    have hUAC : U ⊓ A ≤ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := fun b hb =>
      Subgroup.mem_centralizer_iff.mpr fun a ha => hUab a ha.1 b hb.1
    have hu' : u ∈ (U ⊓ V) ⊔ (U ⊓ A) := hUd ▸ hu
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_centralizer hUAC hu'
    have hbV : b ∈ Subgroup.centralizer (V : Set G) := by
      have ha' : a⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        Subgroup.inv_mem _ (Subgroup.mem_centralizer_iff.mpr fun v hv => hVab v hv a ha.2)
      have := Subgroup.mul_mem _ ha' huV
      simpa using this
    by_cases hb1 : b = 1
    · rw [hb1, mul_one]
      exact ha.2
    · exfalso
      have hbB : b ∈ ASInputs.tiB V A := ⟨hb.2, hUN hb.1⟩
      have h1 := hBase.inf_centralizer_eq' hbB hb1
      apply htiU
      rw [← h1]
      refine le_antisymm inf_le_left fun v hv => ⟨hv, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hbV v hv)
  have hA2 : ((U ⊓ V).subgroupOf V).index = 2 := hidx
  obtain ⟨c₀, hc₀, hc₀1⟩ : ∃ c ∈ (U ⊓ V).subgroupOf V, c ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : (U ⊓ V).subgroupOf V = ⊥ := eq_bot_iff.mpr fun a ha =>
      Subgroup.mem_bot.mpr (hno a ha)
    rw [hbot, Subgroup.index_bot] at hA2
    rw [hA2] at hVn
    rcases hn with rfl | rfl | rfl <;> norm_num at hVn
  have hCVU : V ⊓ Subgroup.centralizer (U : Set G) ≤ U := by
    rintro v ⟨hv, hvU⟩
    by_contra hvU'
    have hvA : (⟨v, hv⟩ : ↥V) ∉ (U ⊓ V).subgroupOf V := fun h1 =>
      hvU' (Subgroup.mem_subgroupOf.mp h1).1
    set t := MulAutTwo.transv hV2' hA2 hc₀ with ht
    have htA : t ∈ transvAxis ((U ⊓ V).subgroupOf V) :=
      ⟨fun _ ha => MulAutTwo.transv_of_mem hV2' hA2 hc₀ ha,
        MulAutTwo.transv_mul_inv_mem hV2' hA2 hc₀⟩
    rw [← htv] at htA
    obtain ⟨⟨u, hu⟩, hut⟩ := (A4.mem_autOn_iff hUN).mp htA
    have h1 := congrArg (fun σ : MulAut ↥V => ((σ ⟨v, hv⟩ : ↥V) : G)) hut
    simp only [A4.actionOn_apply_coe] at h1
    rw [ht, MulAutTwo.transv_of_not_mem hV2' hA2 hc₀ hvA] at h1
    have h2 : u * v * u⁻¹ = v := by
      rw [Subgroup.mem_centralizer_iff.mp hvU u hu]
      group
    rw [h2] at h1
    apply hc₀1
    apply Subtype.ext
    have h3 : (v : G) = v * (c₀ : G) := by
      have := h1
      push_cast at this
      exact this
    have := congrArg (fun y => (v : G)⁻¹ * y) h3
    simpa using this.symm
  have hUCL : U ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hu, huL⟩
    have hcen : A4.actionOn V U hUN ⟨u, hu⟩ ∈ Subgroup.center (MulAut ↥V) := by
      rw [Subgroup.mem_center_iff]
      intro σ
      obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLV).mp (htop ▸ Subgroup.mem_top σ)
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, A4.actionOn_apply_coe, A4.actionOn_apply_coe,
        A4.actionOn_apply_coe, A4.actionOn_apply_coe]
      have hcl := Subgroup.mem_centralizer_iff.mp huL l hl
      calc l * (u * (w : G) * u⁻¹) * l⁻¹ = (l * u) * w * (l * u)⁻¹ := by group
        _ = (u * l) * w * (u * l)⁻¹ := by rw [hcl]
        _ = u * (l * w * l⁻¹) * u⁻¹ := by group
    have h8 : 2 ≤ Nat.card ↥V := by
      rw [hVn]
      rcases hn with rfl | rfl | rfl <;> norm_num
    rw [center_mulAut_eq_bot hV2' h8, Subgroup.mem_bot, A4.actionOn_eq_one_iff] at hcen
    have : u ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hCUV ⟨hu, hcen⟩, huL⟩
    rwa [hCV] at this
  have hCTLU : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (U : Set G) := by
    rintro c ⟨hcS, hcL⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hd1 : c * u * c⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHU (hTH hcS)) u).mp hu) (U.inv_mem hu)
    have hd2 : c * u * c⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      have huN := B6.le_normalizer_centralizer hH.normalizes (hUT hu)
      have h3 := (Subgroup.mem_normalizer_iff.mp huN _).mp (Subgroup.inv_mem _ hcL)
      rw [show c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) by group]
      exact Subgroup.mul_mem _ hcL h3
    have : c * u * c⁻¹ * u⁻¹ ∈ U ⊓ Subgroup.centralizer (L : Set G) := ⟨hd1, hd2⟩
    rw [hUCL, Subgroup.mem_bot] at this
    calc u * c = (c * u * c⁻¹ * u⁻¹)⁻¹ * c * u := by group
      _ = c * u := by rw [this, inv_one, one_mul]
  have hWU : U ⊓ V ≤ U := inf_le_left
  have hW2 : ∀ w ∈ U ⊓ V, w * w = 1 := fun w hw => by rw [← pow_two]; exact hUe.2 w hw.1
  have hPU : ∀ y ∈ (S : Subgroup G), y * h * y⁻¹ ∈ U ⊔ Subgroup.zpowers h := by
    intro y hy
    have h1 : h ∈ oTwoUpper H := by
      rw [hK, hPh]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
    have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH hy)) h).mp h1
    rwa [hK, hPh, sup_comm] at h2
  have hAW : ∀ a ∈ U ⊓ CFSG.conjugate V h, h * a * h⁻¹ ∈ U ⊓ V := fun a ha =>
    ⟨(Subgroup.mem_normalizer_iff.mp hhU a).mp ha.1, BlueprintB2.mem_conjugate_iff.mp ha.2⟩
  have hUP' : U ⊓ Subgroup.centralizer (Subgroup.zpowers h : Set G) = ⊥ := hPh ▸ hUP
  obtain ⟨v₀, hv₀V, hv₀U⟩ : ∃ v₀ ∈ V, v₀ ∉ U := by
    by_contra hno
    push Not at hno
    have htop' : (U ⊓ V).subgroupOf V = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_subgroupOf.mpr ⟨hno x x.2, x.2⟩
    rw [htop', Subgroup.index_top] at hA2
    exact absurd hA2 (by norm_num)
  have hv₀N : v₀ ∈ Subgroup.normalizer (U : Set G) := hHU (hTH (hVT hv₀V))
  have hv₀W : v₀ ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => hVab w hw.2 v₀ hv₀V
  have hv₀c : ∀ u ∈ U, v₀ * u * v₀⁻¹ * u⁻¹ ∈ U ⊓ V := fun u hu =>
    ⟨U.mul_mem ((Subgroup.mem_normalizer_iff.mp hv₀N u).mp hu) (U.inv_mem hu), by
      rw [show v₀ * u * v₀⁻¹ * u⁻¹ = v₀ * (u * v₀⁻¹ * u⁻¹) by group]
      exact V.mul_mem hv₀V ((Subgroup.mem_normalizer_iff.mp (hUN hu) _).mp (V.inv_mem hv₀V))⟩
  obtain h1 | hv₀inv := actionOn_conj_eq_or_eq_inv hp hord hUab hW2 hhU hUP' hU1 hv₀N hv₀W
    hv₀c (hPU v₀ (hVT hv₀V))
  · exact absurd (hCVU ⟨hv₀V, mem_centralizer_of_actionOn_comm hUd hWU hAW hhU hv₀N hv₀W h1⟩)
      hv₀U
  have hQUV : ∀ q ∈ Q, ∃ v ∈ V, v * q ∈ Subgroup.centralizer (U : Set G) := by
    intro q hq
    have hqN : q ∈ Subgroup.normalizer (U : Set G) := hHU (hTH (hQT hq))
    have hqW : q ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun w hw => ((hVQ w hw.2).2 q hq).symm
    have hqc : ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ U ⊓ V := fun u hu =>
      ⟨U.mul_mem ((Subgroup.mem_normalizer_iff.mp hqN u).mp hu) (U.inv_mem hu), by
        have := hQU' q hq u hu
        rwa [commutatorElement_def] at this⟩
    obtain h1 | h1 := actionOn_conj_eq_or_eq_inv hp hord hUab hW2 hhU hUP' hU1 hqN hqW hqc
      (hPU q (hQT hq))
    · exact ⟨1, V.one_mem, by
        rw [one_mul]
        exact mem_centralizer_of_actionOn_comm hUd hWU hAW hhU hqN hqW h1⟩
    · refine ⟨v₀, hv₀V, mem_centralizer_of_actionOn_comm hUd hWU hAW hhU
        (Subgroup.mul_mem _ hv₀N hqN) (Subgroup.mul_mem _ hv₀W hqW) ?_⟩
      have e : (⟨v₀ * q, Subgroup.mul_mem _ hv₀N hqN⟩ : ↥(Subgroup.normalizer (U : Set G))) =
        ⟨v₀, hv₀N⟩ * ⟨q, hqN⟩ := rfl
      rw [e, map_mul]
      exact conj_mul_eq_of_conj_eq_inv hv₀inv h1
  have hQQ : ∀ a ∈ Q, ∀ b ∈ Q, a⁻¹ * b⁻¹ * a * b ∈ Subgroup.centralizer (L : Set G) := by
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hα := hqL a ha l hl
    have hβ := hqL b hb l hl
    have hαb : b * (a * l * a⁻¹ * l⁻¹) * b⁻¹ = a * l * a⁻¹ * l⁻¹ := by
      rw [(hVQ _ hα).2 b hb, mul_inv_cancel_right]
    have hβa : a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ = b * l * b⁻¹ * l⁻¹ := by
      rw [(hVQ _ hβ).2 a ha, mul_inv_cancel_right]
    have hαβ := hVab _ hα _ hβ
    have e1 : (a * b) * l * (a * b)⁻¹ = (b * l * b⁻¹ * l⁻¹) * (a * l * a⁻¹ * l⁻¹) * l := by
      calc (a * b) * l * (a * b)⁻¹ =
          a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ * (a * l * a⁻¹ * l⁻¹) * l := by group
        _ = _ := by rw [hβa]
    have e2 : (b * a) * l * (b * a)⁻¹ = (a * l * a⁻¹ * l⁻¹) * (b * l * b⁻¹ * l⁻¹) * l := by
      calc (b * a) * l * (b * a)⁻¹ =
          b * (a * l * a⁻¹ * l⁻¹) * b⁻¹ * (b * l * b⁻¹ * l⁻¹) * l := by group
        _ = _ := by rw [hαb]
    calc l * (a⁻¹ * b⁻¹ * a * b) = (b * a)⁻¹ * ((b * a) * l * (b * a)⁻¹) * (a * b) := by group
      _ = (b * a)⁻¹ * ((a * b) * l * (a * b)⁻¹) * (a * b) := by rw [e1, e2, hαβ]
      _ = a⁻¹ * b⁻¹ * a * b * l := by group
  have hax : ∀ q' ∈ Q, q' ∈ Subgroup.centralizer (U : Set G) → ∀ (l : G) (hl : l ∈ L),
      A4.actionOn V L hLV ⟨l, hl⟩ ∈ transvAxis ((U ⊓ V).subgroupOf V) →
        q' * l * q'⁻¹ * l⁻¹ = 1 := by
    intro q' hq' hq'U l hl hlt
    rw [← htv] at hlt
    obtain ⟨⟨u, hu⟩, hul⟩ := (A4.mem_autOn_iff hUN).mp hlt
    have hc : l⁻¹ * u ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have e := congrArg (fun σ : MulAut ↥V => ((σ ⟨v, hv⟩ : ↥V) : G)) hul
      simp only [A4.actionOn_apply_coe] at e
      calc v * (l⁻¹ * u) = l⁻¹ * (l * v * l⁻¹) * u := by group
        _ = l⁻¹ * (u * v * u⁻¹) * u := by rw [e]
        _ = l⁻¹ * u * v := by group
    have hcQ : l⁻¹ * u ∈ Q := hCVQ' ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.inv_mem hl))
      (Subgroup.mem_sup_right (hUT hu)), hc⟩
    have hcomm : q' * u = u * q' := (Subgroup.mem_centralizer_iff.mp hq'U u hu).symm
    have he : q' * (l⁻¹ * u)⁻¹ * q'⁻¹ * (l⁻¹ * u) ∈ Subgroup.centralizer (L : Set G) := by
      have := hQQ q'⁻¹ (Q.inv_mem hq') (l⁻¹ * u) hcQ
      rwa [inv_inv] at this
    have key : q' * l * q'⁻¹ * l⁻¹ = u * (q' * (l⁻¹ * u)⁻¹ * q'⁻¹ * (l⁻¹ * u)) * u⁻¹ := by
      calc q' * l * q'⁻¹ * l⁻¹ = (q' * u) * (l⁻¹ * u)⁻¹ * q'⁻¹ * (l⁻¹ * u) * u⁻¹ := by group
        _ = (u * q') * (l⁻¹ * u)⁻¹ * q'⁻¹ * (l⁻¹ * u) * u⁻¹ := by rw [hcomm]
        _ = _ := by group
    have hmemC : q' * l * q'⁻¹ * l⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [key]
      exact (Subgroup.mem_normalizer_iff.mp
        (B6.le_normalizer_centralizer hH.normalizes (hUT hu)) _).mp he
    have hmem : q' * l * q'⁻¹ * l⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hqL q' hq' l hl, hmemC⟩
    rwa [hCV, Subgroup.mem_bot] at hmem
  have hc3a : Q ≤ V ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
    intro q hq
    rcases hn with rfl | hn45
    · obtain ⟨v, hv, hvq⟩ := hQUV q hq
      have hvqQ : v * q ∈ Q := Q.mul_mem (hVQ v hv).1 hq
      obtain ⟨v', hv', hv'q⟩ := exists_mul_mem_centralizer_of_cocycle_axis hLV hV2' le_rfl hVn
        htop (hqL _ hvqQ) (hqC _ hvqQ) hA2 (hax _ hvqQ hvq)
      rw [show q = (v' * v)⁻¹ * (v' * (v * q)) by group]
      exact Subgroup.mul_mem_sup (V.inv_mem (V.mul_mem hv' hv))
        ⟨Subgroup.mul_mem _ (hVT hv') (hQT hvqQ), hv'q⟩
    · have hn4 : 4 ≤ n := by omega
      obtain ⟨v, hv, hvq⟩ := exists_mul_mem_centralizer_of_cocycle hLV hV2' hn4 hVn htop
        (hqL q hq) (hqC q hq)
      rw [show q = v⁻¹ * (v * q) by group]
      exact Subgroup.mul_mem_sup (V.inv_mem hv) ⟨Subgroup.mul_mem _ (hVT hv) (hQT hq), hvq⟩
  have hCLQ : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤ Q := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
      (sup_le ?_ ?_) (S.isPGroup'.to_le inf_le_left)
    · exact (Subgroup.le_centralizer_iff.mp inf_le_right).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer ht, B6.le_normalizer_centralizer hH.normalizes ht⟩
  have hc3 : Q = V ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
    le_antisymm hc3a (sup_le (fun v hv => (hVQ v hv).1) hCLQ)
  have hc2 : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) =
      U ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
    apply le_antisymm
    · rw [hc1]
      refine sup_le le_sup_left fun x hx => ?_
      have hxV : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) :=
        ⟨hx.1, Subgroup.centralizer_le hVI hx.2⟩
      have hxQ : x ∈ V ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := hc3 ▸ hCVQ hxV
      obtain ⟨v, hv, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer
        ((inf_le_right).trans hCLV) hxQ
      have hvU : v ∈ Subgroup.centralizer (U : Set G) := by
        have h1 := Subgroup.centralizer_le hUle hx.2
        have h2 := Subgroup.inv_mem _ (hCTLU hc)
        have := Subgroup.mul_mem _ h1 h2
        simpa using this
      exact Subgroup.mul_mem_sup (hCVU ⟨hv, hvU⟩) hc
    · exact sup_le (le_inf hUT hUC) (le_inf inf_le_left hCTLU)
  have hCIU : (S : Subgroup G) ⊓ Subgroup.centralizer (I : Set G) ≤
      Subgroup.centralizer (U : Set G) := inf_le_right.trans (Subgroup.centralizer_le hUle)
  have hsq : ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G), x * x = 1 := by
    intro x hx
    have hx1 : x ∈ U ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (I : Set G)) := hc1 ▸ hx
    obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hCIU hx1
    have hx2 : u * c ∈ U ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := hc2 ▸ hx
    obtain ⟨u', hu', c', hc', he⟩ := exists_mul_of_mem_sup_centralizer
      (le_inf inf_le_left hCTLU |>.trans inf_le_right) hx2
    have hsqU : ∀ w ∈ U, w * w = 1 := fun w hw => by rw [← pow_two]; exact hUe.2 w hw
    have h1 : (u * c) * (u * c) = c * c := by
      have hcu := Subgroup.mem_centralizer_iff.mp (hCIU hc) u hu
      calc (u * c) * (u * c) = u * (c * u) * c := by group
        _ = u * (u * c) * c := by rw [hcu]
        _ = (u * u) * (c * c) := by group
        _ = c * c := by rw [hsqU u hu, one_mul]
    have h2 : (u * c) * (u * c) = c' * c' := by
      have hcu := Subgroup.mem_centralizer_iff.mp (hCTLU hc') u' hu'
      rw [← he]
      calc (u' * c') * (u' * c') = u' * (c' * u') * c' := by group
        _ = u' * (u' * c') * c' := by rw [hcu]
        _ = (u' * u') * (c' * c') := by group
        _ = c' * c' := by rw [hsqU u' hu', one_mul]
    have h3 : c * c ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ⊓
        Subgroup.centralizer (I : Set G) := by
      refine ⟨⟨Subgroup.mul_mem _ hc.1 hc.1, ?_⟩, Subgroup.mul_mem _ hc.2 hc.2⟩
      rw [← h1, h2]
      exact Subgroup.mul_mem _ hc'.2 hc'.2
    rw [hc4, Subgroup.mem_bot] at h3
    rw [h1, h3]
  have hRab : ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G),
      ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G), a * b = b * a := by
    intro a ha b hb
    have hab := hsq _ (Subgroup.mul_mem _ ha hb)
    have ha1 := hsq a ha
    have hb1 := hsq b hb
    calc a * b = a * b * (b * a) * (b * a) := by
          rw [mul_assoc (a * b), hsq _ (Subgroup.mul_mem _ hb ha), mul_one]
      _ = a * (b * b) * a * (b * a) := by group
      _ = b * a := by rw [hb1, mul_one, ha1, one_mul]
  have hRe : IsElemAbelian 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) :=
    ⟨⟨⟨fun a b => Subtype.ext (hRab a a.2 b b.2)⟩⟩, fun x hx => by rw [pow_two]; exact hsq x hx⟩
  have hCLR : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
      (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := le_inf inf_le_left hCTLU
  have hc8 : (S : Subgroup G) = ((S : Subgroup G) ⊓ L) ⊔
      ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
    apply le_antisymm
    · intro t ht
      obtain ⟨l, hl, c, hc, hlc⟩ :=
        Lem24.exists_mul_of_mem_sup_normal (inf_le_left.trans hH.normalizes) (hTLC ht)
      have hcQ : c ∈ V ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := hc3 ▸ hCVQ hc
      obtain ⟨v, hv, c', hc', hvc⟩ := exists_mul_of_mem_sup_centralizer
        ((inf_le_right).trans hCLV) hcQ
      have e : t = (l * v) * c' := by rw [← hlc, ← hvc]; group
      have hlv : l * v ∈ (S : Subgroup G) := by
        have : l * v = t * c'⁻¹ := by rw [e]; group
        rw [this]
        exact Subgroup.mul_mem _ ht (Subgroup.inv_mem _ hc'.1)
      rw [e]
      exact Subgroup.mul_mem_sup ⟨hlv, L.mul_mem hl (hVL hv)⟩ hc'
    · exact sup_le inf_le_left inf_le_left
  have hCLSL : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => Subgroup.mem_centralizer_iff.mp hx.2 y hy.2
  have hCLZ : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : t ∈ ((S : Subgroup G) ⊓ L) ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
      hc8 ▸ ht
    obtain ⟨t₁, ht₁, c₁, hc₁, rfl⟩ := exists_mul_of_mem_sup_centralizer hCLSL ht'
    have h1 := Subgroup.mem_centralizer_iff.mp hc.2 t₁ ht₁.2
    have h2 := hRab c (hCLR hc) c₁ (hCLR hc₁)
    calc t₁ * c₁ * c = t₁ * (c * c₁) := by rw [mul_assoc, h2]
      _ = c * (t₁ * c₁) := by rw [← mul_assoc, h1, mul_assoc]
  have hpL : pCoreOf 2 L ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (hH.normalizes.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hZ : quasithinOmegaOneCenter (S : Subgroup G) =
      (V ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)) ⊔
        ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
    apply le_antisymm
    · rw [quasithinOmegaOneCenter, Subgroup.closure_le]
      rintro z ⟨⟨hzS, hzC⟩, -⟩
      have hz' : z ∈ ((S : Subgroup G) ⊓ L) ⊔
          ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := hc8 ▸ hzS
      obtain ⟨t₁, ht₁, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hCLSL hz'
      have ht₁C : t₁ ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
        have := Subgroup.mul_mem _ hzC (Subgroup.inv_mem _ (hCLZ hc))
        simpa using this
      have ht₁V : t₁ ∈ Subgroup.centralizer (V : Set G) := Subgroup.centralizer_le hVT ht₁C
      have ht₁Q : t₁ ∈ V ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
        hc3 ▸ hpL (hCLV' ⟨ht₁.2, ht₁V⟩)
      obtain ⟨v, hv, c₂, hc₂, rfl⟩ := exists_mul_of_mem_sup_centralizer
        ((inf_le_right).trans hCLV) ht₁Q
      have hvC : v ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
        have := Subgroup.mul_mem _ ht₁C (Subgroup.inv_mem _ (hCLZ hc₂))
        simpa using this
      rw [mul_assoc]
      exact Subgroup.mul_mem_sup ⟨hv, hvC⟩ (Subgroup.mul_mem _ hc₂ hc)
    · refine sup_le (fun v hv => Subgroup.subset_closure ⟨⟨hVT hv.1, hv.2⟩, hVe.2 v hv.1⟩)
        (fun c hc => Subgroup.subset_closure ⟨⟨hc.1, hCLZ hc⟩, by
          rw [pow_two]; exact hsq c (hCLR hc)⟩)
  have hCIZ : (S : Subgroup G) ⊓ Subgroup.centralizer (I : Set G) ≤
      quasithinOmegaOneCenter (S : Subgroup G) := by
    intro x hx
    have hxR : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := ⟨hx.1, hCIU hx⟩
    have hx2 : x ∈ U ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := hc2 ▸ hxR
    have hxC : x ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨u, hu, c, hc, hx'⟩ := exists_mul_of_mem_sup_centralizer
        (le_inf inf_le_left hCTLU |>.trans inf_le_right) hx2
      have hcC := Subgroup.mem_centralizer_iff.mp (hCLZ hc)
      have hd1 : x * t * x⁻¹ * t⁻¹ ∈ U := by
        rw [← hx', show u * c * t * (u * c)⁻¹ * t⁻¹ = u * (c * t * c⁻¹) * u⁻¹ * t⁻¹ by group,
          show c * t * c⁻¹ = t by rw [← hcC t ht]; group]
        have := (Subgroup.mem_normalizer_iff.mp (hHU (hTH ht)) u⁻¹).mp (U.inv_mem hu)
        rw [show u * t * u⁻¹ * t⁻¹ = u * (t * u⁻¹ * t⁻¹) by group]
        exact U.mul_mem hu this
      have hd2 : x * t * x⁻¹ * t⁻¹ ∈ Subgroup.centralizer (I : Set G) := by
        have htN := B6.le_normalizer_centralizer hHI (hTH ht)
        have h3 := (Subgroup.mem_normalizer_iff.mp htN _).mp (Subgroup.inv_mem _ hx.2)
        rw [show x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) by group]
        exact Subgroup.mul_mem _ hx.2 h3
      have : x * t * x⁻¹ * t⁻¹ ∈ U ⊓ Subgroup.centralizer (I : Set G) := ⟨hd1, hd2⟩
      rw [hc1b, Subgroup.mem_bot] at this
      calc t * x = (x * t * x⁻¹ * t⁻¹)⁻¹ * x * t := by group
        _ = x * t := by rw [this, inv_one, one_mul]
    exact Subgroup.subset_closure ⟨⟨hx.1, hxC⟩, by rw [pow_two]; exact hsq x hxR⟩
  have hcardIL : Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (I : Set G)) =
      Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
    have h1 := card_sup_eq_mul hCIU (eq_bot_iff.mpr (hc1b ▸ inf_le_inf_left _ inf_le_right))
    have h2 := card_sup_eq_mul (le_inf inf_le_left hCTLU |>.trans inf_le_right)
      (eq_bot_iff.mpr (hUCL ▸ inf_le_inf_left _ inf_le_right))
    rw [← hc1] at h1
    rw [← hc2] at h2
    rw [h1] at h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  have hc10 : Nat.card ↥(V ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)) = 2 := by
    obtain ⟨-, hSLodd⟩ := A7.sylow_inf_of_le_normalizer S hH.normalizes
    set α := A4.actionOn V L hLV with hα
    have hαs : Function.Surjective α := by
      intro σ
      obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).mp (htop ▸ Subgroup.mem_top σ)
      exact ⟨l, hl⟩
    set X := (((S : Subgroup G) ⊓ L).subgroupOf L).map α with hX
    have hXodd : ¬ 2 ∣ X.index := fun h2 => hSLodd (h2.trans (Subgroup.index_map_dvd _ hαs))
    have hfix : ∀ v (hv : v ∈ V ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)),
        ∀ σ ∈ X, σ ⟨v, hv.1⟩ = ⟨v, hv.1⟩ := by
      rintro v hv _ ⟨l, hl, rfl⟩
      apply Subtype.ext
      rw [hα, A4.actionOn_apply_coe]
      have := Subgroup.mem_centralizer_iff.mp hv.2 l (Subgroup.mem_subgroupOf.mp hl).1
      show (l : G) * v * (l : G)⁻¹ = v
      rw [this]
      group
    have huniq : ∀ a (ha : a ∈ V ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G))
        b (hb : b ∈ V ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)), a ≠ 1 → b ≠ 1 →
        a = b := by
      intro a ha b hb ha1 hb1
      have := eq_of_fixed_of_odd_index hV2' hXodd (x := ⟨a, ha.1⟩) (y := ⟨b, hb.1⟩)
        (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
        (hfix a ha) (hfix b hb)
      exact congrArg Subtype.val this
    have hne : V ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) ≠ ⊥ := by
      have h1 := Lem7.omegaOneCenter_inf_ne_bot hH.sylow.1 hVT hTV hH.irrPlus.2.1
        (fun v hv => hVe.2 v hv)
      intro h0
      apply h1
      rw [eq_bot_iff, ← h0]
      rintro z ⟨hz, hzV⟩
      refine ⟨hzV, ?_⟩
      have hZC : quasithinOmegaOneCenter (S : Subgroup G) ≤
          Subgroup.centralizer ((S : Subgroup G) : Set G) :=
        (Subgroup.closure_le _).mpr fun w hw => hw.1.2
      exact hZC hz
    obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    have heq : V ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) = Subgroup.zpowers a₀ := by
      apply le_antisymm
      · intro b hb
        by_cases hb1 : b = 1
        · rw [hb1]; exact Subgroup.one_mem _
        · rw [huniq b hb a₀ ha₀ hb1 ha₀1']
          exact Subgroup.mem_zpowers a₀
      · exact (Subgroup.zpowers_le).mpr ha₀
    rw [heq, Nat.card_zpowers]
    exact orderOf_eq_prime (hVe.2 a₀ ha₀.1) ha₀1'
  have hc6 : Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 := by
    have hcomm12 : (S : Subgroup G) ⊓ Subgroup.centralizer (I : Set G) ≤
        Subgroup.centralizer (((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) :
          Subgroup G) : Set G) := fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hRab y (hCLR hy) x ⟨hx.1, hCIU hx⟩
    have h1 := card_sup_eq_mul hcomm12 (by
      rw [eq_bot_iff, ← hc4]
      exact fun x hx => ⟨hx.1, hx.2.2⟩)
    have h2 : ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) ⊔
        ((S : Subgroup G) ⊓ Subgroup.centralizer (I : Set G)) ≤
          quasithinOmegaOneCenter (S : Subgroup G) :=
      sup_le (hZ ▸ le_sup_right) hCIZ
    have h3 := card_sup_eq_mul (((inf_le_right).trans hCLV).trans
      (Subgroup.centralizer_le inf_le_left) :
        (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
          Subgroup.centralizer ((V ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) :
            Subgroup G) : Set G))
      (eq_bot_iff.mpr (hCV ▸ inf_le_inf inf_le_left inf_le_right))
    rw [← hZ, hc10] at h3
    have h4 := Subgroup.card_le_of_le h2
    rw [h1, h3, hcardIL] at h4
    have hpos : 0 < Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.card_pos
    nlinarith
  have hUQ : (L ⊔ (S : Subgroup G)) ⊓ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) ≤
      U ⊔ Q := by
    rintro x ⟨hxLT, hxW⟩
    have hσW : ∀ a ∈ (U ⊓ V).subgroupOf V,
        A4.actionOn V (L ⊔ (S : Subgroup G)) (sup_le hLV hTV) ⟨x, hxLT⟩ a = a := fun a ha =>
      Subtype.ext (by
        have := Subgroup.mem_centralizer_iff.mp hxW a (Subgroup.mem_subgroupOf.mp ha)
        show x * (a : G) * x⁻¹ = a
        rw [← this, mul_inv_cancel_right])
    have hσt : A4.actionOn V (L ⊔ (S : Subgroup G)) (sup_le hLV hTV) ⟨x, hxLT⟩ ∈
        transvAxis ((U ⊓ V).subgroupOf V) := by
      refine ⟨hσW, fun y => ?_⟩
      rw [Subgroup.mul_mem_iff_of_index_two hA2]
      by_cases hy : y ∈ (U ⊓ V).subgroupOf V
      · exact iff_of_true (by rw [hσW y hy]; exact hy) (Subgroup.inv_mem _ hy)
      · refine iff_of_false (fun h1 => hy ?_) (fun h1 => hy (inv_mem_iff.mp h1))
        have h2 := hσW _ h1
        rwa [(MulEquiv.injective _ h2)] at h1
    rw [← htv] at hσt
    obtain ⟨⟨u, hu⟩, hux⟩ := (A4.mem_autOn_iff hUN).mp hσt
    have hc : u⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have e := congrArg (fun τ : MulAut ↥V => ((τ ⟨v, hv⟩ : ↥V) : G)) hux
      simp only [A4.actionOn_apply_coe] at e
      calc v * (u⁻¹ * x) = u⁻¹ * (u * v * u⁻¹) * x := by group
        _ = u⁻¹ * (x * v * x⁻¹) * x := by rw [e]
        _ = u⁻¹ * x * v := by group
    rw [show x = u * (u⁻¹ * x) by group]
    exact Subgroup.mul_mem_sup hu (hCVQ' ⟨Subgroup.mul_mem _
      (Subgroup.mem_sup_right (hUT (U.inv_mem hu))) hxLT, hc⟩)
  have hidx2 : ∀ v ∈ V, v ∉ U → v₀⁻¹ * v ∈ U := by
    intro v hv hvU
    have ha : ((⟨v₀, hv₀V⟩ : ↥V)⁻¹ : ↥V) ∉ (U ⊓ V).subgroupOf V := fun h1 =>
      hv₀U (inv_mem_iff.mp (Subgroup.mem_subgroupOf.mp h1).1)
    have hb : (⟨v, hv⟩ : ↥V) ∉ (U ⊓ V).subgroupOf V := fun h1 =>
      hvU (Subgroup.mem_subgroupOf.mp h1).1
    have h1 := (Subgroup.mul_mem_iff_of_index_two hA2).mpr (iff_of_false ha hb)
    exact (Subgroup.mem_subgroupOf.mp h1).1
  have hJ1 : ∀ y ∈ U ⊔ Q, y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ∨
      v₀⁻¹ * y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := by
    intro y hy
    obtain ⟨u, hu, k, hk, rfl⟩ := Lem24.exists_mul_of_mem_sup_normal
      (fun k hk => hHU (hTH (hQT hk))) hy
    have hk' : k ∈ V ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := hc3 ▸ hk
    obtain ⟨v, hv, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer
      ((inf_le_right).trans hCLV) hk'
    by_cases hvU : v ∈ U
    · left
      rw [hc2, ← mul_assoc]
      exact Subgroup.mul_mem_sup (U.mul_mem hu hvU) hc
    · right
      have hu' : v₀⁻¹ * u * v₀ ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hv₀N) u).mp hu
        rwa [inv_inv] at this
      rw [hc2, show v₀⁻¹ * (u * (v * c)) = (v₀⁻¹ * u * v₀) * (v₀⁻¹ * v) * c by group]
      exact Subgroup.mul_mem_sup (U.mul_mem hu' (hidx2 v hv hvU)) hc
  have hJ2 : ∀ b, v₀⁻¹ * b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) →
      ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G), x * b = b * x →
        x ∈ (U ⊓ V) ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
    intro b hb x hx hxb
    have h2 : x * v₀⁻¹ = v₀⁻¹ * x := by
      have h1 : x * (v₀⁻¹ * b) = (v₀⁻¹ * b) * x := hRab x hx _ hb
      calc x * v₀⁻¹ = x * (v₀⁻¹ * b) * b⁻¹ := by group
        _ = (v₀⁻¹ * b) * x * b⁻¹ := by rw [h1]
        _ = v₀⁻¹ * (b * x) * b⁻¹ := by group
        _ = v₀⁻¹ * (x * b) * b⁻¹ := by rw [hxb]
        _ = v₀⁻¹ * x := by group
    have hxv₀ : x * v₀ = v₀ * x := by
      calc x * v₀ = v₀ * (v₀⁻¹ * x) * v₀ := by group
        _ = v₀ * (x * v₀⁻¹) * v₀ := by rw [h2]
        _ = v₀ * x := by group
    have hx2 : x ∈ U ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := hc2 ▸ hx
    obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer
      (le_inf inf_le_left hCTLU |>.trans inf_le_right) hx2
    have hcv : c * v₀ = v₀ * c := (Subgroup.mem_centralizer_iff.mp (hCLV hc.2) v₀ hv₀V).symm
    have huv₀ : u * v₀ = v₀ * u := by
      calc u * v₀ = u * (v₀ * c) * c⁻¹ := by group
        _ = u * (c * v₀) * c⁻¹ := by rw [← hcv]
        _ = u * c * v₀ * c⁻¹ := by group
        _ = v₀ * (u * c) * c⁻¹ := by rw [hxv₀]
        _ = v₀ * u := by group
    have huV : u ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      by_cases hvU : v ∈ U
      · exact hUab v hvU u hu
      · have hvv := hidx2 v hv hvU
        calc v * u = v₀ * ((v₀⁻¹ * v) * u) := by group
          _ = v₀ * (u * (v₀⁻¹ * v)) := by rw [hUab _ hvv u hu]
          _ = (v₀ * u) * (v₀⁻¹ * v) := by group
          _ = (u * v₀) * (v₀⁻¹ * v) := by rw [huv₀]
          _ = u * v := by group
    exact Subgroup.mul_mem_sup ⟨hu, hCUV ⟨hu, huV⟩⟩ hc
  have hRcard : Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) =
      Nat.card ↥U * Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
    have h2 := card_sup_eq_mul (le_inf inf_le_left hCTLU |>.trans inf_le_right)
      (eq_bot_iff.mpr (hUCL ▸ inf_le_inf_left _ inf_le_right))
    rwa [← hc2] at h2
  have hWC : Nat.card ↥((U ⊓ V) ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G))) =
      Nat.card ↥(U ⊓ V) * Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
    card_sup_eq_mul (fun c hc => Subgroup.centralizer_le inf_le_right (hCLV hc.2))
      (eq_bot_iff.mpr (by rw [← hCV]; exact fun x hx => ⟨hx.1.2, hx.2.2⟩))
  have hUcard : Nat.card ↥U = Nat.card ↥(U ⊓ V) * Nat.card ↥(U ⊓ CFSG.conjugate V h) := by
    have h1 := card_sup_eq_mul (fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      hUab a ha.1 b hb.1 : U ⊓ CFSG.conjugate V h ≤
        Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G)) hUi
    rwa [← hUd] at h1
  have hAcard : Nat.card ↥(U ⊓ CFSG.conjugate V h) = Nat.card ↥(U ⊓ V) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨h * a * h⁻¹, hAW a a.2⟩
        invFun := fun w => ⟨h⁻¹ * w * h, ?_, ?_⟩
        left_inv := fun a => Subtype.ext (by show h⁻¹ * (h * (a : G) * h⁻¹) * h = a; group)
        right_inv := fun w => Subtype.ext (by show h * (h⁻¹ * (w : G) * h) * h⁻¹ = w; group) }
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhU) w).mp w.2.1
      rwa [inv_inv] at this
    · refine BlueprintB2.mem_conjugate_iff.mpr ?_
      rw [show h * (h⁻¹ * (w : G) * h) * h⁻¹ = w by group]
      exact w.2.2
  have hWcard : Nat.card ↥(U ⊓ V) * 2 = 2 ^ n := by
    have h1 := Subgroup.card_mul_index ((U ⊓ V).subgroupOf V)
    rw [hA2, hVn, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
    exact h1
  have hJ : ∀ g ∈ L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G),
      ∀ r ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G),
        g * r * g⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := by
    intro g hg r hr
    have hconjUQ : ∀ r' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G),
        g * r' * g⁻¹ ∈ U ⊔ Q := fun r' hr' => hUQ
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hg.1)
        (Subgroup.mem_sup_right hr'.1)) (Subgroup.mem_sup_left (L.inv_mem hg.1)),
       (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_centralizer inf_le_right hg) _).mp
        (Subgroup.centralizer_le inf_le_left hr'.2)⟩
    by_contra hb
    have hbR := (hJ1 _ (hconjUQ r hr)).resolve_left hb
    have hcomm : ∀ r' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G),
        g * r' * g⁻¹ * (g * r * g⁻¹) = (g * r * g⁻¹) * (g * r' * g⁻¹) := fun r' hr' => by
      calc g * r' * g⁻¹ * (g * r * g⁻¹) = g * (r' * r) * g⁻¹ := by group
        _ = g * (r * r') * g⁻¹ := by rw [hRab r' hr' r hr]
        _ = g * r * g⁻¹ * (g * r' * g⁻¹) := by group
    have hmem1 : ∀ r' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G),
        g * r' * g⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) →
          g * r' * g⁻¹ ∈ (U ⊓ V) ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
      fun r' hr' h1 => hJ2 _ hbR _ h1 (hcomm r' hr')
    have hmem2 : ∀ r' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G),
        g * r' * g⁻¹ ∉ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) →
          (g * r * g⁻¹)⁻¹ * (g * r' * g⁻¹) ∈
            (U ⊓ V) ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
      intro r' hr' h1
      have h2 := (hJ1 _ (hconjUQ r' hr')).resolve_left h1
      have h3 : (g * r * g⁻¹)⁻¹ * (g * r' * g⁻¹) ∈
          (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := by
        rw [show (g * r * g⁻¹)⁻¹ * (g * r' * g⁻¹) =
          (v₀⁻¹ * (g * r * g⁻¹))⁻¹ * (v₀⁻¹ * (g * r' * g⁻¹)) by group]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hbR) h2
      refine hJ2 _ hbR _ h3 ?_
      calc (g * r * g⁻¹)⁻¹ * (g * r' * g⁻¹) * (g * r * g⁻¹) =
          (g * r * g⁻¹)⁻¹ * (g * r' * g⁻¹ * (g * r * g⁻¹)) := by group
        _ = (g * r * g⁻¹)⁻¹ * ((g * r * g⁻¹) * (g * r' * g⁻¹)) := by rw [hcomm r' hr']
        _ = (g * r * g⁻¹) * ((g * r * g⁻¹)⁻¹ * (g * r' * g⁻¹)) := by group
    classical
    let f : ↥((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) →
        Bool × ↥((U ⊓ V) ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G))) := fun r' =>
      if h1 : g * (r' : G) * g⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) then
        (false, ⟨_, hmem1 r' r'.2 h1⟩)
      else (true, ⟨_, hmem2 r' r'.2 h1⟩)
    have hf : Function.Injective f := by
      intro x y hxy
      simp only [f] at hxy
      split_ifs at hxy with h1 h2 h2
      · have := congrArg (fun z => (z.2 : G)) hxy
        exact Subtype.ext (by simpa using this)
      · simp at hxy
      · simp at hxy
      · have := congrArg (fun z => (z.2 : G)) hxy
        exact Subtype.ext (by simpa using this)
    have hcard := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hRcard, hWC,
      hUcard, hAcard] at hcard
    have hn8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h4 : 4 ≤ Nat.card ↥(U ⊓ V) := by omega
    have hCpos : 0 < Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.card_pos
    have h5 : 4 * (Nat.card ↥(U ⊓ V) *
          Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G))) ≤
        Nat.card ↥(U ⊓ V) * Nat.card ↥(U ⊓ V) *
          Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_right _ h4
    have h6 : 0 < Nat.card ↥(U ⊓ V) *
        Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.mul_pos (by omega) hCpos
    linarith
  have hc11 : oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) ⊔
      (S : Subgroup G) ≤ Subgroup.normalizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
    refine sup_le ((oTwoUpper_le _).trans fun g hg => ?_) fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer ht, B6.le_normalizer_centralizer hHU (hTH ht)⟩
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hJ g hg r hr, fun hr => ?_⟩
    have := hJ g⁻¹ (Subgroup.inv_mem _ hg) _ hr
    rwa [show g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r by group] at this
  exact ⟨hc1, hc1b, hc2, hUCL, hc3, hCV, hc4, hRe, hc6, hc8, hZ, hc10, hc11⟩

end CFSG.Quasithin.H13
