module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAbel
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddNatAct
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SylowL34

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SL2Model
open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem sq_mem_centralizer_of_commutator_mem {Q L V : Subgroup G}
    (hQV : Q ≤ Subgroup.centralizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hQL : ∀ q ∈ Q, ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ V) {q : G} (hq : q ∈ Q) :
    q ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  set w := q * l * q⁻¹ * l⁻¹ with hwdef
  have hw : w ∈ V := hQL q hq l hl
  have hwq : q * w = w * q := (Subgroup.mem_centralizer_iff.mp (hQV hq) w hw).symm
  have hw2 : w * w = 1 := by
    have := hV.2 w hw
    rwa [pow_two] at this
  have hwl : q * l * q⁻¹ = w * l := by rw [hwdef]; group
  have key : q ^ 2 * l = l * q ^ 2 := by
    calc q ^ 2 * l = q * (q * l * q⁻¹) * q := by rw [pow_two]; group
      _ = q * (w * l) * q := by rw [hwl]
      _ = (q * w) * l * q := by group
      _ = (w * q) * l * q := by rw [hwq]
      _ = w * (q * l * q⁻¹) * q * q := by group
      _ = w * (w * l) * q * q := by rw [hwl]
      _ = (w * w) * l * q * q := by group
      _ = l * q ^ 2 := by rw [hw2, pow_two]; group
  exact key.symm

end General

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem T_inf_centralizer_L_eq_bot (h5114 : Stmt5_1_14_first) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hZL := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.2
  have hT2 : IsPGroup 2 T := (hh.isSylowTwoOf le_top).2.1
  by_contra hne
  have hTC : T ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    hh.T_le_normalizer.trans (normalizer_le_normalizer_centralizer'' L)
  have hTX : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp (hTC ht) x).mp hx.2⟩
  obtain ⟨z, hzX, hz1, hzT⟩ := exists_ne_one_mem_centralizer hT2 inf_le_left hTX hne
  have hzle : Subgroup.zpowers z ≤ (T ⊓ Subgroup.centralizer (L : Set G)) ⊓
      Subgroup.centralizer (T : Set G) := Subgroup.zpowers_le.mpr ⟨hzX, hzT⟩
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    hT2.to_le (hzle.trans (inf_le_left.trans inf_le_left))
  have hdvd : 2 ∣ Nat.card (Subgroup.zpowers z) := by
    rcases hz2.card_eq_or_dvd with h1 | h1
    · exfalso
      apply hz1
      have := (Subgroup.card_eq_one.mp h1)
      have hzm : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
      rw [this, Subgroup.mem_bot] at hzm
      exact hzm
    · exact h1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers z)) 2 hdvd
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyZ : (y : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := by
    have hyX := hzle y.2
    refine ⟨mem_quasithinOmegaOneCenter_iff.mpr ⟨hyX.1.1, hyX.2, ?_⟩, hyX.1.2⟩
    rw [← hy']
    exact pow_orderOf_eq_one _
  rw [hZL, Subgroup.mem_bot] at hyZ
  rw [hyZ, orderOf_one] at hy'
  exact absurd hy' (by norm_num)

theorem commutator_mem_of_block (hblock : ⁅pCoreOf 2 L, L⁆ ≤ V) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) {l : G} (hl : l ∈ L) : q * l * q⁻¹ * l⁻¹ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := by
    rw [hQdef, ← hh.centralizer_eq_pCoreOf s.hyp.module]
    exact inf_le_right
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hh.T_le_normalizer
  have hQLT : Q ≤ L ⊔ T := pCoreOf_le 2 _
  have hQLO : ∀ q ∈ Q, ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro q hq l hl
    refine hh.inf_centralizer_le s.L_le_normalizer_V s.hyp.module.2.2 ⟨?_, ?_⟩
    · have h1 : q * l * q⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hLTL (hQLT hq)) l).mp hl
      exact L.mul_mem h1 (L.inv_mem hl)
    · have h1 : l * q⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        (Subgroup.mem_normalizer_iff.mp
          ((s.L_le_normalizer_V.trans (normalizer_le_normalizer_centralizer'' V)) hl) q⁻¹).mp
          (Subgroup.inv_mem _ (hQC hq))
      have := (Subgroup.centralizer (V : Set G)).mul_mem (hQC hq) h1
      simpa [mul_assoc] using this
  have hodd : ∀ x ∈ L, Odd (orderOf x) → ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ V := by
    intro x hx hxo q hq
    have hXQ : Subgroup.zpowers x ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.zpowers_le.mpr (hLQ hx)
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card Q) := by
      obtain ⟨k, hk⟩ := hQ2.exists_card_eq
      rw [Nat.card_zpowers, hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hxo)
    have hid := coprime_commutator_commutator_eq hXQ hcop
    have hmem : ⁅q, x⁆ ∈ ⁅Q, Subgroup.zpowers x⁆ :=
      Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)
    rw [← hid] at hmem
    have hle : ⁅⁅Q, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ ≤ V := by
      refine (Subgroup.commutator_mono ?_ (Subgroup.zpowers_le.mpr hx)).trans hblock
      rw [Subgroup.commutator_le]
      intro q' hq' y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [commutatorElement_def]
      exact hQLO q' hq' _ (L.zpow_mem hx i)
    have := hle hmem
    rwa [commutatorElement_def] at this
  have hLeq : L = oTwoUpper L :=
    (hh.faithful.2.1 _ (oTwoUpper_le L)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
        (le_normalizer_oTwoUpper L)) fun x hx => exists_pow_mem_oTwoUpper L hx).symm
  have hlO : l ∈ oTwoUpper L := hLeq ▸ hl
  have hVN : ∀ x ∈ L, ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun x hx v hv =>
    (Subgroup.mem_normalizer_iff.mp (s.L_le_normalizer_V hx) v).mp hv
  suffices hall : ∀ q ∈ Q, q * l * q⁻¹ * l⁻¹ ∈ V from hall q hq
  clear hq hl
  induction hlO using Subgroup.closure_induction with
  | mem x hx =>
    exact fun q hq => hodd x hx.1 hx.2 q hq
  | one =>
    intro q _
    simp
  | mul x y hx hy ihx ihy =>
    intro q hq
    have hxL : x ∈ L := oTwoUpper_le L hx
    have e : q * (x * y) * q⁻¹ * (x * y)⁻¹ =
        (q * x * q⁻¹ * x⁻¹) * (x * (q * y * q⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact V.mul_mem (ihx q hq) (hVN x hxL _ (ihy q hq))
  | inv x hx ihx =>
    intro q hq
    have hxL : x ∈ L := oTwoUpper_le L hx
    have e : q * x⁻¹ * q⁻¹ * x⁻¹⁻¹ = x⁻¹ * (q * x * q⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact hVN _ (L.inv_mem hxL) _ (V.inv_mem (ihx q hq))

theorem mem_centralizer_of_mem_centralizer_D (hI : L2OddInnerFact) (hF : L2TorusFact) {t : G}
    (ht : t ∈ T) (htD : t ∈ Subgroup.centralizer (D : Set G)) :
    t ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨c⟩ := s.nonempty_coord
  have hh := s.hyp.hyp.toHyp5_0_1
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  let tn : Subgroup.normalizer (V : Set G) := ⟨t, s.T_le_normalizer ht⟩
  show (tn : G) ∈ Subgroup.centralizer (V : Set G)
  rw [s.mem_centralizer_iff_of_T hI c tn ht]
  have key := s.T_act_eq hI c tn ht
  generalize (c.act tn ![0, 1]) 0 = b at key ⊢
  obtain ⟨μ, hμ0, hμ1⟩ : ∃ μ : c.K, μ ≠ 0 ∧ μ ^ 2 ≠ 1 := by
    rcases card_two_or_exists_sq_ne_one (F := c.K) with h2 | h
    · exfalso
      rw [c.card] at h2
      have hn2 : 2 ≤ n := hh.two_le
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    · exact h
  obtain ⟨d, hdD, hd⟩ := s.exists_D_act_eq hI hF c hμ0
  obtain ⟨A, hA0, hA⟩ := s.exists_mat_of_normalizer hI c d (hDL hdD) (s.D_le_normalizer_Z₁ hI hdD)
  have hA11 : (A : Matrix (Fin 2) (Fin 2) c.K) 1 1 = μ := by
    have h1 := hd ![0, 1]
    rw [hA, mulVec_one_of_lower _ hA0] at h1
    simpa using h1
  have hA00 : (A : Matrix (Fin 2) (Fin 2) c.K) 0 0 * μ = 1 := by
    rw [← hA11]
    exact mul_eq_one_of_lower A hA0
  have hdt : d * tn = tn * d := Subtype.ext (Subgroup.mem_centralizer_iff.mp htD d hdD)
  have h1 : c.act d (c.act tn ![0, 1]) = c.act tn (c.act d ![0, 1]) := by
    rw [← c.act_mul, ← c.act_mul, hdt]
  rw [key ![0, 1], key (c.act d ![0, 1]), hA, hA] at h1
  have h2 := congrFun h1 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hA0, hA11] at h2
  have h3 : b * (μ ^ 2 - 1) = 0 := by linear_combination (-μ) * h2 + b * hA00
  exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr hμ1)

theorem not_commutator_pCoreOf_le (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first) : ¬ ⁅pCoreOf 2 L, L⁆ ≤ V := by
  intro hblock
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hQT : Q ≤ T := by
    rw [hQdef, ← hh.centralizer_eq_pCoreOf s.hyp.module]
    exact inf_le_left
  have hQ2 : ∀ q ∈ Q, q ^ 2 = 1 := by
    intro q hq
    have hQC : Q ≤ Subgroup.centralizer (V : Set G) := by
      rw [hQdef, ← hh.centralizer_eq_pCoreOf s.hyp.module]
      exact inf_le_right
    have h1 := sq_mem_centralizer_of_commutator_mem hQC s.elemAbelian
      (fun q hq l hl => s.commutator_mem_of_block hblock hq hl) hq
    have h2 : q ^ 2 ∈ T ⊓ Subgroup.centralizer (L : Set G) := ⟨T.pow_mem (hQT hq) 2, h1⟩
    rw [s.T_inf_centralizer_L_eq_bot h5114, Subgroup.mem_bot] at h2
    exact h2
  have hinv : ∀ q ∈ Q, q⁻¹ = q := fun q hq => by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hQ2 q hq]
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ := (hinv _ (Q.mul_mem hx hy)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv y hy, hinv x hx]
  have hCQ : ∀ t ∈ T, t ∈ Subgroup.centralizer (D : Set G) → t ∈ Q := fun t ht htD => by
    rw [hQdef, ← hh.centralizer_eq_pCoreOf s.hyp.module]
    exact ⟨ht, s.mem_centralizer_of_mem_centralizer_D hI hF ht htD⟩
  set P := T ⊓ K with hPdef
  have hDT : D ≤ Subgroup.normalizer (T : Set G) :=
    s.hyp.notation59.2.1.1.trans (hh.borelL_le_normalizer_T_of_odd hI s.odd)
  have hDK : D ≤ Subgroup.normalizer (K : Set G) := s.D_le_normalizer
  have hDP : D ≤ Subgroup.normalizer (P : Set G) := by
    intro d hd
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hDT hd) x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (hDK hd) x).mp hx.2⟩
  have hP2 : IsPGroup 2 P := (hh.isSylowTwoOf le_top).2.1.to_le inf_le_left
  have hPsolv : Group.IsSolvable ↥P := by
    have := hP2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card D) (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr s.hyp.notation59.2.1.2.1)
  have hfac := coprime_le_commutator_sup_inf_centralizer hDP hPsolv hcop
  have hPD : ⁅P, D⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro p hp d hd
    have := (pCoreOf 2 K).inv_mem
      (commutator_mem_of_mem_centralizerModO2 (s.D_le_centralizer hd) hp.2)
    have e : (d * p * d⁻¹ * p⁻¹)⁻¹ = ⁅p, d⁆ := by rw [commutatorElement_def]; group
    rwa [e] at this
  have hPsyl : IsSylowTwoOf P K :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf s.hyp.hyp.hStar.1.1) (oTwoUpper_le H)
      (le_normalizer_oTwoUpper H)
  let π : ↥K →* O2Q K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ P.subgroupOf K := by
    intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    exact (pCoreOf_two_le_of_isSylowTwoOf hPsyl) ⟨x, hx, rfl⟩
  set S := (P.subgroupOf K).map π with hSdef
  have hS : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, (hPsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPsyl.1).symm).map π, ?_⟩
    show ¬ 2 ∣ S.relIndex ⊤
    rw [Subgroup.relIndex_top_right, hSdef, Subgroup.index_map_eq _ hπs hker]
    exact hPsyl.2.2
  have hSab : IsMulCommutative S := by
    set A := P ⊓ Subgroup.centralizer (D : Set G) with hAdef
    have hAK : A ≤ K := inf_le_left.trans inf_le_right
    have hPDK : ⁅P, D⁆ ≤ K := hPD.trans (pCoreOf_le 2 K)
    have hSle : S ≤ (A.subgroupOf K).map π := by
      have h1 : P.subgroupOf K ≤ ⁅P, D⁆.subgroupOf K ⊔ A.subgroupOf K := by
        rw [← Subgroup.subgroupOf_sup hPDK hAK]
        intro x hx
        exact hfac hx
      have h2 : (⁅P, D⁆.subgroupOf K).map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        intro x hx
        rw [QuotientGroup.ker_mk']
        have hx' : (x : G) ∈ pCoreOf 2 K := hPD hx
        obtain ⟨y, hy, hyx⟩ := hx'
        have : y = x := Subtype.ext hyx
        rwa [← this]
      calc S = (P.subgroupOf K).map π := rfl
        _ ≤ (⁅P, D⁆.subgroupOf K ⊔ A.subgroupOf K).map π := Subgroup.map_mono h1
        _ = (A.subgroupOf K).map π := by rw [Subgroup.map_sup, h2, bot_sup_eq]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x, hx, hxa⟩ := hSle a.2
    obtain ⟨y, hy, hyb⟩ := hSle b.2
    have hxy : x * y = y * x := Subtype.ext
      (hQab _ (hCQ _ hx.1.1 hx.2) _ (hCQ _ hy.1.1 hy.2))
    show (a : O2Q K) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  exact not_isMulCommutative_of_isSylowTwoOf s.hyp.l34 hS hSab

end Setup5_1_17Odd

theorem stmt5_1_17_noBlock_of (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first) : Stmt5_1_17_noBlock :=
  fun _ _ _ _ _ _ _ _ _ _ _ s => s.not_commutator_pCoreOf_le hI hF h5114

theorem stmt5_1_17_abelian_proved (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first) (h126 : A126TwoFact) : Stmt5_1_17_abelian :=
  stmt5_1_17_abelian_of hI hF h5114 h126 (stmt5_1_17_noBlock_of hI hF h5114)

end CFSG.Quasithin.H13
