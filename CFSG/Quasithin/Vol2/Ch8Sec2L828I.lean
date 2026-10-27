module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828H
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch8Sec2L828D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

section L828I

variable {G : Type} [Group G] [Finite G]

theorem altDn5_ker_828 : (FFModel.altDn 5).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  have ha2 : G6.allOnes 5 * G6.allOnes 5 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    show (1 : ZMod 2) + 1 = 0
    decide
  have hinv : (G6.allOnes 5)⁻¹ = G6.allOnes 5 := inv_eq_of_mul_eq_one_right ha2
  have hzp : ∀ y ∈ Subgroup.zpowers (G6.allOnes 5), y = 1 ∨ y = G6.allOnes 5 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    induction k using Int.induction_on with
    | zero => left; simp
    | succ i ih =>
      rw [zpow_add_one]
      rcases ih (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _) with h | h
      · right; rw [h, one_mul]
      · left; rw [h, ha2]
    | pred i ih =>
      rw [zpow_sub_one]
      rcases ih (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _) with h | h
      · right; rw [h, one_mul]; exact hinv
      · left; rw [h]; exact mul_inv_cancel _
  have hnot : G6.allOnes 5 ∉ G6.coreMod 5 := by
    rw [G6.mem_coreMod]
    decide
  rcases hzp x hx1 with h | h
  · exact h
  · exact absurd (h ▸ hx2) hnot

theorem exists_equiv_alt5_828 {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    (hX : AlternatingNatural X ⊤ ⊥ 5) :
    ∃ e : W ≃* ↥(G6.coreMod 5), X.map (MulAut.congr e).toMonoidHom = alt5D_828.range := by
  obtain ⟨π, hπs, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := hX
  have hker : (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = ⊥ := by
    rw [altDn5_ker_828]
    exact Subgroup.bot_subgroupOf _
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e₁ := MulEquiv.ofBijective β ⟨hβi, hβs⟩
  let e₂ := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientBot (G := ↥(G6.coreMod 5)))
  let e : W ≃* ↥(G6.coreMod 5) := Subgroup.topEquiv.symm.trans (e₁.trans e₂)
  have hequiv : ∀ (γ : ↥(alternatingGroup (Fin 5))) (w : W),
      e (((π γ : ↥X) : MulAut W) w) = G6.coreAct 5 (γ : Equiv.Perm (Fin 5)) (e w) := by
    intro γ w
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, Subgroup.mem_top w⟩)
    have h1 := hβe γ ⟨w, Subgroup.mem_top w⟩ m (Subgroup.mem_top _) (hsec γ m m.2) hm.symm
    have hew : e w = m := by
      show e₂ (β ⟨w, Subgroup.mem_top w⟩) = m
      rw [← hm]
      rfl
    rw [hew]
    show e₂ (β ⟨_, Subgroup.mem_top _⟩) = _
    rw [h1]
    rfl
  have hcongr : ∀ (γ : ↥(alternatingGroup (Fin 5))),
      (MulAut.congr e) ((π γ : ↥X) : MulAut W) = alt5D_828 γ := by
    intro γ
    ext v
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hequiv,
      MulEquiv.apply_symm_apply, alt5D_828_apply]
  refine ⟨e, ?_⟩
  ext f
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    refine ⟨γ, ?_⟩
    have h := hcongr γ
    rw [hγ] at h
    exact h.symm
  · rintro ⟨γ, rfl⟩
    exact ⟨_, (π γ).2, hcongr γ⟩

theorem eq_of_le_alternatingNatural_828 {W : Type} [CommGroup W]
    {X Y : Subgroup (MulAut W)} (hX : AlternatingNatural X ⊤ ⊥ 5) (hXY : X ≤ Y)
    (hperf : ⁅Y, Y⁆ = Y) (h9 : ¬ 9 ∣ Nat.card Y) : Y = X := by
  obtain ⟨e, he⟩ := exists_equiv_alt5_828 hX
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have h1 : alt5D_828.range ≤ Y.map (MulAut.congr e).toMonoidHom :=
    he ▸ Subgroup.map_mono hXY
  have h2 : ⁅Y.map (MulAut.congr e).toMonoidHom, Y.map (MulAut.congr e).toMonoidHom⁆ =
      Y.map (MulAut.congr e).toMonoidHom := by
    rw [← Subgroup.map_commutator, hperf]
  have h3 : ¬ 9 ∣ Nat.card ↥(Y.map (MulAut.congr e).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective hinj]
  have h4 := eq_range_alt5D_828 h1 h2 h3
  rw [← he] at h4
  exact Subgroup.map_injective hinj h4

theorem not_commute_dihedral_828 {Q : Type*} [Group Q] {m : ℕ} (hm : Odd m)
    (e : Q ≃* DihedralGroup m) {a b : Q} (ha : a ≠ 1) (ha2 : a ^ 2 = 1) (hb : b ≠ 1)
    (hb3 : b ^ 3 = 1) : ¬ Commute a b := by
  intro hab
  have h2 : IsUnit (2 : ZMod m) := by
    have hc : Nat.Coprime 2 m := Nat.Coprime.symm (Nat.coprime_two_right.mpr hm)
    exact (ZMod.unitOfCoprime 2 hc).isUnit
  have h2z : ∀ j : ZMod m, j + j = 0 → j = 0 := fun j hj => by
    rw [← two_mul] at hj
    exact (h2.mul_right_eq_zero).mp hj
  have hea : e a ≠ 1 := fun h => ha (e.injective (h.trans (map_one e).symm))
  have heb : e b ≠ 1 := fun h => hb (e.injective (h.trans (map_one e).symm))
  have hea2 : e a ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  have heb3 : e b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hcomm : e a * e b = e b * e a := by rw [← map_mul, ← map_mul, hab.eq]
  generalize e a = x at hea hea2 hcomm
  generalize e b = y at heb heb3 hcomm
  rcases x with i | i <;> rcases y with j | j
  · apply hea
    rw [pow_two, DihedralGroup.r_mul_r] at hea2
    rw [DihedralGroup.one_def] at hea2 ⊢
    rw [h2z i (DihedralGroup.r.inj hea2)]
  · apply heb
    rw [pow_succ, pow_two, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr, sub_self,
      sub_zero] at heb3
    exact absurd (heb3.trans DihedralGroup.one_def) (fun h => by cases h)
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at hcomm
    have hj : j + j = 0 := by
      have := DihedralGroup.sr.inj hcomm
      linear_combination this
    apply heb
    rw [DihedralGroup.one_def, h2z j hj]
  · apply heb
    rw [pow_succ, pow_two, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr, sub_self,
      sub_zero] at heb3
    exact absurd (heb3.trans DihedralGroup.one_def) (fun h => by cases h)

theorem exists_sylow_normalized_828 {p : ℕ} [Fact p.Prime] {K B : Subgroup G}
    (hBp : IsPGroup p ↥B) (hBK : B ≤ Subgroup.normalizer (K : Set G)) :
    ∃ Q : Sylow p ↥K, ∀ b ∈ B, ∀ q : ↥K, q ∈ (Q : Subgroup ↥K) →
      ∃ q' ∈ (Q : Subgroup ↥K), (q' : G) = b * (q : G) * b⁻¹ := by
  classical
  let φ : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBK)
  let _ : MulDistribMulAction ↥B ↥K := MulDistribMulAction.compHom ↥K φ
  let _ : MulAction ↥B (Sylow p ↥K) := Sylow.pointwiseMulAction
  have hcard : ¬ p ∣ Nat.card (Sylow p ↥K) := by
    intro h
    have h1 := card_sylow_modEq_one p ↥K
    have h2 : Nat.card (Sylow p ↥K) % p = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.ModEq, h2, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at h1
    exact zero_ne_one h1
  obtain ⟨Q₀, hQ₀⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p ↥K) hcard
  refine ⟨Q₀, fun b hb q hq => ?_⟩
  have hfix : (⟨b, hb⟩ : ↥B) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
  have hmem : (⟨b, hb⟩ : ↥B) • q ∈ (Q₀ : Subgroup ↥K) := by
    have h := Subgroup.smul_mem_pointwise_smul q (⟨b, hb⟩ : ↥B) (Q₀ : Subgroup ↥K) hq
    rwa [← Sylow.pointwise_smul_def, hfix] at h
  refine ⟨_, hmem, ?_⟩
  change (((K.normalizerMonoidHom) (Subgroup.inclusion hBK ⟨b, hb⟩)) q : G) = _
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

theorem eq_of_forall_mul_828 {U B K T : Subgroup G} (hB : B ∈ cComp (B ⊔ T)) (hBK : B ≤ K)
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G)))
    (hKn : (K.subgroupOf (Subgroup.normalizer (U : Set G))).Normal)
    (hTS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (U : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hBC : ¬ B ≤ Subgroup.centralizer (U : Set G))
    (hact : ∀ k ∈ K, ∃ b ∈ B, b⁻¹ * k ∈ Subgroup.centralizer (U : Set G)) : K = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := le_of_mem_cComp hK
  have hNC : Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hKBC : ∀ k ∈ K, ∃ b ∈ B, b⁻¹ * k ∈ K ⊓ Subgroup.centralizer (U : Set G) := by
    intro k hk
    obtain ⟨b, hb, hbk⟩ := hact k hk
    exact ⟨b, hb, Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem (hBK hb)) hk, hbk⟩⟩
  have hCn : ((K ⊓ Subgroup.centralizer (U : Set G)).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf Subgroup.le_normalizer (hKN.trans hNC)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hCne : K ⊓ Subgroup.centralizer (U : Set G) ≠ K := fun e =>
    hBC (hBK.trans (by rw [← e]; exact inf_le_right))
  have hKBO := le_sup_pCoreOf_828 hq (perfect_of_mem_cComp hK) hBK inf_le_left hCn hCne hKBC
  have hNK : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mp hKn
  have hOT : pCoreOf 2 K ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKN)
      (hNK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)).trans
      (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTS)
  exact eq_of_le_sup_828 hB hK hBK (hKBO.trans (sup_le_sup_left hOT B))

end L828I

end CFSG.Quasithin.H13
