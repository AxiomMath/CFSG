module

public import CFSG.Quasithin.Vol2.Ch12Sec6Lemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimTheta
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimPerm
public import CFSG.Quasithin.Background.B5FinS8Schur
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S152UAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 Equiv
open scoped IsMulCommutative

namespace S126Ex

@[expose] def blk (i : Fin 8) : Bool := decide (i.val < 4)

theorem perm_apply_inv (σ : Perm (Fin 8)) (x : Fin 8) : σ (σ⁻¹ x) = x := by
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

@[expose] def presSub : Subgroup (Perm (Fin 8)) where
  carrier := {σ | (∀ i, σ (partner i) = partner (σ i)) ∧
    ∀ i j, (blk i = blk j ↔ blk (σ i) = blk (σ j))}
  one_mem' := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩
  mul_mem' := fun {σ τ} hσ hτ => ⟨fun i => by
      rw [Perm.mul_apply, Perm.mul_apply, hτ.1, hσ.1],
    fun i j => (hτ.2 i j).trans (hσ.2 _ _)⟩
  inv_mem' := fun {σ} hσ => ⟨fun i => by
      apply σ.injective
      rw [perm_apply_inv, hσ.1, perm_apply_inv],
    fun i j => by
      have := hσ.2 (σ⁻¹ i) (σ⁻¹ j)
      rw [perm_apply_inv, perm_apply_inv] at this
      exact this.symm⟩

theorem P8_le_presSub : CFSG.QuasithinUnique.Claim2526.P8 ≤ presSub := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  change g ∈ CFSG.QuasithinUnique.Claim2526.p8Gens at hg
  simp only [CFSG.QuasithinUnique.Claim2526.p8Gens, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

theorem presPart_of_mem {σ : Perm (Fin 8)} (h : σ ∈ presSub) : PresPart σ := by
  refine ⟨h.1, ?_⟩
  have hb : ∀ i : Fin 8, i.val < 4 → blk (σ i) = blk (σ 0) := fun i hi =>
    (h.2 i 0).1 (by simp [blk, hi])
  by_cases h0 : (σ 0).val < 4
  · left
    intro i hi
    have := hb i hi
    simp only [blk, h0, decide_true, decide_eq_true_eq] at this
    exact this
  · right
    intro i hi
    have := hb i hi
    simp only [blk, h0, decide_false, decide_eq_false_iff_not, not_lt] at this
    exact this

theorem exists_conj_le_P8 {Q : Subgroup (Perm (Fin 8))} (hQ : IsPGroup 2 Q) :
    ∃ g : Perm (Fin 8), ∀ q ∈ Q, g⁻¹ * q * g ∈ CFSG.QuasithinUnique.Claim2526.P8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfact : (Nat.card (Perm (Fin 8))).factorization 2 = 7 := by
    rw [CFSG.QuasithinUnique.Claim2526.card_perm_fin8, show (40320 : ℕ) = 2 ^ 7 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  let S : Sylow 2 (Perm (Fin 8)) := Sylow.ofCard CFSG.QuasithinUnique.Claim2526.P8 (by
    rw [CFSG.QuasithinUnique.Claim2526.card_P8, hfact]
    norm_num)
  obtain ⟨Q', hQ'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 8)) S Q'
  refine ⟨g, fun q hq => ?_⟩
  have hq' : q ∈ (Q' : Subgroup (Perm (Fin 8))) := hQ' hq
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq'
  simpa [S, MulAut.smul_def, MulAut.conj_inv_apply, mul_assoc] using hq'

theorem ker8_eq : B5FinS8.Ker8 = natKer 8 := by
  ext x
  change (x : PermMod 8) ∈ Subgroup.zpowers (allOnes 8) ⊓ coreMod 8 ↔
    (x : PermMod 8) ∈ Subgroup.zpowers (allOnes 8)
  exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩

@[expose] noncomputable def e8 : B5FinS8.Mod8 ≃* D8 := QuotientGroup.quotientMulEquivOfEq ker8_eq

theorem e8_act (σ : Perm (Fin 8)) (q : B5FinS8.Mod8) :
    e8 (B5FinS8.act8 σ q) = dAct σ (e8 q) := by
  induction q using QuotientGroup.induction_on with
  | H m =>
    rw [B5FinS8.act8_mk]
    change (QuotientGroup.mk _ : D8) = QuotientGroup.map (natKer 8) (natKer 8)
      (coreAct 8 σ).toMonoidHom _ (QuotientGroup.mk m)
    rw [QuotientGroup.map_mk]
    congr 1

theorem act8_mul (σ τ : Perm (Fin 8)) (q : B5FinS8.Mod8) :
    B5FinS8.act8 (σ * τ) q = B5FinS8.act8 σ (B5FinS8.act8 τ q) :=
  DFunLike.congr_fun ((FFModel.symDn_isActionModel 8).modEnd_mul σ τ) q

theorem act8_one (q : B5FinS8.Mod8) : B5FinS8.act8 1 q = q :=
  DFunLike.congr_fun (FFModel.symDn_isActionModel 8).modEnd_one q

theorem act8_inv_act8 (σ : Perm (Fin 8)) (q : B5FinS8.Mod8) :
    B5FinS8.act8 σ⁻¹ (B5FinS8.act8 σ q) = q := by
  rw [← act8_mul, inv_mul_cancel, act8_one]

theorem act8_act8_inv (σ : Perm (Fin 8)) (q : B5FinS8.Mod8) :
    B5FinS8.act8 σ (B5FinS8.act8 σ⁻¹ q) = q := by
  rw [← act8_mul, mul_inv_cancel, act8_one]

end S126Ex

open S126Ex

variable {G : Type} [Group G]

theorem frame126Exists_of (h1222 : Stmt12_2_2) : Frame126Exists := by
  intro G _ _ T L V hH
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  obtain ⟨hc, π₀, hπ₀, -, -, -, -, -, -, β₀, hβs, hβk, hβe⟩ := hH.module
  let π₁ : ↥(alternatingGroup (Fin 8)) →* ↥(autOn L V) := π₀
  have hπ₁ : Function.Surjective π₁ := hπ₀
  let β₁ : ↥(⊤ : Subgroup ↥V) →* B5FinS8.Mod8 := β₀
  have hβ₁s : Function.Surjective β₁ := hβs
  have hβ₁k : ∀ u : ↥(⊤ : Subgroup ↥V),
      β₁ u = 1 ↔ (u : ↥V) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V := hβk
  have hβ₁e : ∀ (σ : ↥(alternatingGroup (Fin 8))) (u : ↥(⊤ : Subgroup ↥V)) (m : ↥(coreMod 8)),
      β₁ u = QuotientGroup.mk m →
        β₁ ⟨(π₁ σ : MulAut ↥V) u, Subgroup.mem_top _⟩ =
          QuotientGroup.mk ⟨permAct 8 σ m, permAct_mem_coreMod _ m.2⟩ :=
    fun σ u m h => hβe σ u m _ _ h
  have hcard : Nat.card ↥(autOn L V) = Nat.card ↥(alternatingGroup (Fin 8)) := by
    obtain ⟨φ, hφ, hker⟩ := hH.alt8
    have hk : (InternalSec.autOnHom hLV).ker = φ.ker := by
      rw [hker]
      ext l
      rw [InternalSec.mem_ker_autOnHom, Subgroup.mem_subgroupOf]
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (InternalSec.autOnHom_surjective hLV)).toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hk).toEquiv
  have hπinj : Function.Injective π₁ := by
    obtain ⟨e⟩ := Finite.card_eq.1 hcard.symm
    exact (Finite.injective_iff_surjective_of_equiv e).2 hπ₁
  let πE : ↥(alternatingGroup (Fin 8)) ≃* ↥(autOn L V) := MulEquiv.ofBijective π₁ ⟨hπinj, hπ₁⟩
  let βV : ↥V →* B5FinS8.Mod8 :=
    { toFun := fun v => β₁ ⟨v, Subgroup.mem_top v⟩
      map_one' := map_one β₁
      map_mul' := fun a b => map_mul β₁ ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩ }
  have hβV : ∀ v, βV v = β₁ ⟨v, Subgroup.mem_top v⟩ := fun _ => rfl
  have hβVs : Function.Surjective βV := by
    intro q
    obtain ⟨u, hu⟩ := hβ₁s q
    exact ⟨(u : ↥V), hu⟩
  have hβVk : ∀ v : ↥V, βV v = 1 ↔ (v : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro v
    rw [hβV, hβ₁k]
    rfl
  have hβVe : ∀ (σ : ↥(alternatingGroup (Fin 8))) (v : ↥V),
      βV ((πE σ : MulAut ↥V) v) = B5FinS8.act8 σ (βV v) := by
    intro σ v
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (βV v)
    have h1 := hβ₁e σ ⟨v, Subgroup.mem_top v⟩ m hm.symm
    rw [← hm, B5FinS8.act8_mk]
    exact h1
  have hTN : autOn T V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
    autOn_le_normalizer_autOn hTV hLV hTL
  let θ := CFSG.QuasithinUnique.Claim2526.thetaHom (autOn L V) πE.symm
  let ρ : ↥(autOn T V) →* Perm (Fin 8) := θ.comp (Subgroup.inclusion hTN)
  have hρ2 : IsPGroup 2 ρ.range :=
    (CFSG.Quasithin.isPGroup_autOn hyp.sylow.1 hTV).of_surjective ρ.rangeRestrict
      ρ.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := exists_conj_le_P8 hρ2
  have hT : ∀ (a : ↥(autOn T V)) (v : ↥V),
      βV ((a : MulAut ↥V) v) = B5FinS8.act8 (ρ a) (βV v) := by
    intro a v
    obtain ⟨t, ht, htT, hta⟩ := mem_autOn_iff_exists.mp a.2
    have hZ : ∀ w : ↥V, βV w = 1 → βV ((a : MulAut ↥V) w) = 1 := by
      intro w hw
      rw [hβVk] at hw ⊢
      rw [← hta]
      change t * (w : G) * t⁻¹ ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff] at hw ⊢
      intro l hl
      have hl' : t⁻¹ * l * t ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hTL (T.inv_mem htT)) l).1 hl
        simpa using this
      have := hw _ hl'
      calc l * (t * (w : G) * t⁻¹) = t * ((t⁻¹ * l * t) * w) * t⁻¹ := by group
        _ = t * (w * (t⁻¹ * l * t)) * t⁻¹ := by rw [this]
        _ = t * (w : G) * t⁻¹ * l := by group
    have hZ' : ∀ w : ↥V, βV ((a : MulAut ↥V) w) = 1 → βV w = 1 := by
      intro w hw
      rw [hβVk] at hw ⊢
      rw [← hta] at hw
      change t * (w : G) * t⁻¹ ∈ Subgroup.centralizer (L : Set G) at hw
      rw [Subgroup.mem_centralizer_iff] at hw ⊢
      intro l hl
      have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTL htT) l).1 hl
      have := hw _ hl'
      have e1 : l * (w : G) = t⁻¹ * ((t * l * t⁻¹) * (t * (w : G) * t⁻¹)) * t := by group
      have e2 : (w : G) * l = t⁻¹ * ((t * (w : G) * t⁻¹) * (t * l * t⁻¹)) * t := by group
      rw [e1, e2, this]
    let A : ↥V →* ↥V := (a : MulAut ↥V).toMonoidHom
    have hker : βV.ker ≤ βV.ker.comap A := fun w hw => hZ w hw
    let eβ := QuotientGroup.quotientKerEquivOfSurjective βV hβVs
    let τ : B5FinS8.Mod8 →* B5FinS8.Mod8 :=
      eβ.toMonoidHom.comp ((QuotientGroup.map βV.ker βV.ker A hker).comp eβ.symm.toMonoidHom)
    have hτ : ∀ w, τ (βV w) = βV ((a : MulAut ↥V) w) := by
      intro w
      have h1 : eβ.symm (βV w) = QuotientGroup.mk w := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      change eβ (QuotientGroup.map βV.ker βV.ker A hker (eβ.symm (βV w))) = _
      rw [h1, QuotientGroup.map_mk]
      rfl
    have hτinj : Function.Injective τ := by
      rw [injective_iff_map_eq_one]
      intro q hq
      obtain ⟨w, rfl⟩ := hβVs q
      rw [hτ] at hq
      exact hZ' w hq
    have hspec := CFSG.QuasithinUnique.Claim2526.theta_spec (autOn L V) πE.symm
      (Subgroup.inclusion hTN a)
    have hcomm : ∀ σ : Perm (Fin 8), σ ∈ alternatingGroup (Fin 8) → ∀ q : B5FinS8.Mod8,
        τ (B5FinS8.act8 σ q) = B5FinS8.act8 (ρ a * σ * (ρ a)⁻¹) (τ q) := by
      intro σ hσ q
      obtain ⟨w, rfl⟩ := hβVs q
      set σ' : ↥(alternatingGroup (Fin 8)) := ⟨σ, hσ⟩
      have h1 := hspec (πE σ')
      rw [MulEquiv.symm_apply_apply] at h1
      set k : ↥(autOn L V) := (autOn L V).normalizerMonoidHom (Subgroup.inclusion hTN a) (πE σ')
      have hk : (k : MulAut ↥V) = (a : MulAut ↥V) * (πE σ' : MulAut ↥V) * (a : MulAut ↥V)⁻¹ :=
        rfl
      have h2 : πE (πE.symm k) = k := MulEquiv.apply_symm_apply _ _
      have e1 : (a : MulAut ↥V) ((πE σ' : MulAut ↥V) w) =
          (k : MulAut ↥V) ((a : MulAut ↥V) w) := by
        rw [hk]
        simp [MulAut.mul_apply]
      rw [← hβVe σ' w, hτ, hτ, e1, ← h2, hβVe]
      exact congrArg (fun π => B5FinS8.act8 π (βV ((a : MulAut ↥V) w))) h1
    let μ : B5FinS8.Mod8 →* B5FinS8.Mod8 := (B5FinS8.act8 (ρ a)⁻¹).comp τ
    have hμinj : Function.Injective μ := by
      intro q₁ q₂ h
      apply hτinj
      have := congrArg (B5FinS8.act8 (ρ a)) h
      simpa only [μ, MonoidHom.comp_apply, act8_act8_inv] using this
    have hμ := B5FinS8.k8 μ hμinj (fun σ hσ q => by
      change B5FinS8.act8 (ρ a)⁻¹ (τ (B5FinS8.act8 σ q)) =
        B5FinS8.act8 σ (B5FinS8.act8 (ρ a)⁻¹ (τ q))
      rw [hcomm σ hσ q, ← act8_mul, ← act8_mul]
      congr 1
      group)
    have := congrArg (B5FinS8.act8 (ρ a)) (hμ (βV v))
    simp only [μ, MonoidHom.comp_apply, act8_act8_inv] at this
    rw [← hτ, this]
  let conjg : MulAut ↥(alternatingGroup (Fin 8)) := MulAut.conjNormal g
  have hconjg : ∀ σ : ↥(alternatingGroup (Fin 8)),
      ((conjg σ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) = g * σ * g⁻¹ := fun _ => rfl
  refine ⟨hc, ⟨{
    π := πE.toMonoidHom.comp conjg.toMonoidHom
    π_surj := πE.surjective.comp conjg.surjective
    β := e8.toMonoidHom.comp ((B5FinS8.act8 g⁻¹).comp βV)
    β_surj := ?_
    β_ker := ?_
    equi := ?_
    tAct := ?_ }⟩⟩
  · intro y
    obtain ⟨v, hv⟩ := hβVs (B5FinS8.act8 g (e8.symm y))
    refine ⟨v, ?_⟩
    change e8 (B5FinS8.act8 g⁻¹ (βV v)) = y
    rw [hv, act8_inv_act8, MulEquiv.apply_symm_apply]
  · intro v
    change e8 (B5FinS8.act8 g⁻¹ (βV v)) = 1 ↔ _
    rw [← hβVk, ← map_one e8, e8.injective.eq_iff]
    constructor
    · intro h
      have := congrArg (B5FinS8.act8 g) h
      rwa [act8_act8_inv, map_one] at this
    · intro h
      rw [h, map_one]
  · intro σ v
    change e8 (B5FinS8.act8 g⁻¹ (βV ((πE (conjg σ) : MulAut ↥V) v))) =
      dAct σ (e8 (B5FinS8.act8 g⁻¹ (βV v)))
    rw [hβVe, ← e8_act, hconjg, ← act8_mul, ← act8_mul]
    congr 1
    group
  · intro t ht
    have hta : conjAct V ⟨t, hTV ht⟩ ∈ autOn T V :=
      mem_autOn_iff_exists.mpr ⟨t, hTV ht, ht, rfl⟩
    set a : ↥(autOn T V) := ⟨_, hta⟩
    refine ⟨g⁻¹ * ρ a * g, presPart_of_mem (P8_le_presSub (hg _ ⟨a, rfl⟩)), fun v w hvw => ?_⟩
    have hw : w = (a : MulAut ↥V) v := Subtype.ext hvw
    change e8 (B5FinS8.act8 g⁻¹ (βV w)) = dAct (g⁻¹ * ρ a * g) (e8 (B5FinS8.act8 g⁻¹ (βV v)))
    rw [hw, hT, ← e8_act, ← act8_mul, ← act8_mul]
    congr 1
    group

end CFSG.Quasithin.H13
