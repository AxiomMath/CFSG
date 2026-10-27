module

public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedCharts
public import CFSG.LocalAnalysis.StandardType.GGF4ReflPairFrameOrd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.StandardType.GGF4CoxeterSystem
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGF4ReflLin
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen
import CFSG.LocalAnalysis.StandardType.GGRowKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootPerm
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.StandardType.GGF4FrameData

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

section Helpers

variable {G : Type} [Group G]

private theorem ggMulAut_eq_of_eq_on_sup {Bs H₁ H₂ : Subgroup G} (h₁le : H₁ ≤ Bs)
    (h₂le : H₂ ≤ Bs) (hB : Bs = H₁ ⊔ H₂) {φ ψ : MulAut ↥Bs}
    (h₁ : ∀ b : ↥Bs, (b : G) ∈ H₁ → φ b = ψ b) (h₂ : ∀ b : ↥Bs, (b : G) ∈ H₂ → φ b = ψ b) :
    φ = ψ := by
  have htop : Subgroup.closure
      ((H₁.subgroupOf Bs : Set ↥Bs) ∪ (H₂.subgroupOf Bs : Set ↥Bs)) = ⊤ := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
      ← Subgroup.subgroupOf_sup h₁le h₂le, ← hB, Subgroup.subgroupOf_self]
  have h := MonoidHom.eq_of_eqOn_dense (f := φ.toMonoidHom) (g := ψ.toMonoidHom) htop
    (by
      rintro b (hb | hb)
      · exact h₁ b hb
      · exact h₂ b hb)
  ext b
  exact congrArg Subtype.val (DFunLike.congr_fun h b)

private theorem ggIsReflection_five_of_le_fix [Finite G] {Bs : Subgroup G}
    (hBsE : IsElemAbelian 5 Bs) (hcard : Nat.card Bs = 625) {τ : MulAut ↥Bs} (hτ2 : τ ^ 2 = 1)
    {H : Subgroup G} (hHB : H ≤ Bs) (hH : Nat.card H = 125)
    (hfix : ∀ b : ↥Bs, (b : G) ∈ H → τ b = b) {b₀ : ↥Bs} (hb₀ : τ b₀ ≠ b₀) :
    GGIsReflection 5 τ := by
  have hiff : ∀ b : ↥Bs, ((b : G) ∈ ggFixG Bs τ ↔ τ b = b) := by
    intro b
    constructor
    · intro hb
      rcases Subgroup.mem_map.mp hb with ⟨c, hc, hcb⟩
      have hcb' : c = b := Subtype.ext hcb
      rw [← hcb']
      exact hc
    · intro hb
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
  have hle : H ≤ ggFixG Bs τ := fun h hh =>
    (hiff ⟨h, hHB hh⟩).2 (hfix ⟨h, hHB hh⟩ hh)
  have hfle : ggFixG Bs τ ≤ Bs := Subgroup.map_subtype_le _
  have hne : ggFixG Bs τ ≠ Bs := by
    intro h
    have hb : (b₀ : G) ∈ ggFixG Bs τ := by
      rw [h]
      exact b₀.2
    exact hb₀ ((hiff b₀).1 hb)
  have hcard' : Nat.card Bs ≤ 5 * Nat.card (ggFixG Bs τ) := by
    have := Subgroup.card_le_of_le hle
    rw [hcard]
    omega
  exact isReflection_of_fix_iff_mem Nat.prime_five hfle hBsE hcard' hne hτ2 hiff

private theorem ggMulAut_commute_of_split {Bs D E : Subgroup G} (hD : D ≤ Bs) (hE : E ≤ Bs)
    (hB : Bs = D ⊔ E) {φ ψ : MulAut ↥Bs} (hφD : ∀ b : ↥Bs, (b : G) ∈ D → ((φ b : ↥Bs) : G) ∈ D)
    (hφE : ∀ b : ↥Bs, (b : G) ∈ E → φ b = b) (hψD : ∀ b : ↥Bs, (b : G) ∈ D → ψ b = b)
    (hψE : ∀ b : ↥Bs, (b : G) ∈ E → ((ψ b : ↥Bs) : G) ∈ E) : φ * ψ = ψ * φ := by
  refine ggMulAut_eq_of_eq_on_sup hD hE hB (fun b hb => ?_) (fun b hb => ?_)
  · rw [MulAut.mul_apply, MulAut.mul_apply, hψD b hb, hψD (φ b) (hφD b hb)]
  · rw [MulAut.mul_apply, MulAut.mul_apply, hφE b hb, hφE (ψ b) (hψE b hb)]

end Helpers

section Alignment


theorem ggF4N2_swap_exchanges_axes_of_inverters
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hginv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hgx : g * x * g⁻¹ = x)
    {t₁ t₂ j₁ j₂ s : G} (hj₁ : j₁ ∈ Subgroup.normalizer (Bs : Set G))
    (hj₂ : j₂ ∈ Subgroup.normalizer (Bs : Set G)) (hs : s ∈ Subgroup.normalizer (Bs : Set G))
    (hj₁J : j₁ ∈ J) (hj₂J : j₂ ∈ J) (hsK : s ∈ K) (ht₁ : t₁ ∈ Bs ⊓ J) (ht₂ : t₂ ∈ Bs ⊓ J)
    (ht₁o : orderOf t₁ = 5) (ht₂o : orderOf t₂ = 5) (h₁₁ : j₁ * t₁ * j₁⁻¹ = t₁⁻¹)
    (h₁₂ : j₁ * t₂ * j₁⁻¹ = t₂) (h₂₁ : j₂ * t₁ * j₂⁻¹ = t₁) (h₂₂ : j₂ * t₂ * j₂⁻¹ = t₂⁻¹)
    (hj₁₂ : j₁ * j₂ = j₂ * j₁) (hsj : s * j₁ * s⁻¹ = j₂) :
    ∃ v : G, v ∈ D ⊓ K ∧ orderOf v = 5 ∧ D = Subgroup.zpowers y ⊔ Subgroup.zpowers v ∧
      g * y * g⁻¹ ∈ Subgroup.zpowers v ∧
      ∃ t ∈ K, t ∈ Subgroup.normalizer (Bs : Set G) ∧ t ∈ Subgroup.centralizer (J : Set G) ∧
        t * y * t⁻¹ = y ∧ t * v * t⁻¹ = v⁻¹ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hcfg : GGConfig 5 B Bs x L D J := hR.1
  have hBsE : IsElemAbelian 5 Bs := hcfg.2.1.2.1
  have hNT : GGNoTransvection 5 Bs := hR.2.2.2.1
  have hcard : Nat.card Bs = 625 := by
    have h := (ggF4N2Rank hR hL).1
    norm_num at h
    exact h
  obtain ⟨hxBs, hxy, hyo, hDcl, hDcard, hDE⟩ := ggF4N2_x_data hR hNbr
  have hDeq : D = Bs ⊓ Subgroup.centralizer (J : Set G) := ggF4N2_D_eq_Bs_inf_centralizer_J hR hL
  have hDBs : D ≤ Bs := hDeq ▸ inf_le_left
  have hDC : ∀ d ∈ D, ∀ j ∈ J, j * d * j⁻¹ = d := by
    intro d hd j hj
    have hdC : d ∈ Subgroup.centralizer (J : Set G) := (hDeq ▸ hd : d ∈ Bs ⊓ _).2
    rw [Subgroup.mem_centralizer_iff.mp hdC j hj]
    group
  have hyD : y ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hxD : x ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hyBs : y ∈ Bs := hDBs hyD
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyo
    norm_num at hyo
  have hx1 : x ≠ 1 := fun h => hxy (h ▸ Subgroup.one_mem _)
  obtain ⟨hBsDJ, hDJ, hBJ25, -⟩ := ggF4N2J_original_torus_split hR hNbr hL hK
  have hJK : J ≤ K := ggF4N2J_le_psl6_neighbor hR hNbr hL hK
  have hJL : J ≤ L := fun j hj => (hcfg.2.2.1.2.2.2.2.2.1.1 hj).1
  have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) := ggF4N2_Bs_le_normalizer_K hR hNbr hL
  obtain ⟨a, haD, hao₀, hDxa, -, hga, hgND, -⟩ := ggF4N2L_swap_normalizes hR hL hgL hginv hgx
  have hao : orderOf (a : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hao₀
  obtain ⟨t, htK, htN, htJ, htND, hty, htA, htR, -, -, v, hvD, hvo, hvinv, hvne⟩ :=
    ggF4N2K_exists_original_inverter_reflection hR hNbr hL hK
  have hDJbot : D ⊓ J = ⊥ := disjoint_iff.mp hDJ
  have hcomm : ∀ u ∈ Bs, ∀ w ∈ Bs, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hBsE.1.is_comm.comm (⟨u, hu⟩ : ↥Bs) ⟨w, hw⟩)
  have hBJE : IsElemAbelian 5 (Bs ⊓ J) :=
    ⟨⟨⟨fun u w => Subtype.ext (hcomm u u.2.1 w w.2.1)⟩⟩, fun u hu => hBsE.2 u hu.1⟩
  have ht₁1 : t₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht₁o
    norm_num at ht₁o
  have ht₂1 : t₂ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht₂o
    norm_num at ht₂o
  have hinv_ne : ∀ u : G, orderOf u = 5 → u⁻¹ ≠ u := by
    intro u hu h
    have h2 : u ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← h]; exact inv_mul_cancel u
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [hu] at hdvd
    norm_num at hdvd
  have hpow_inv : ∀ (n u : G), n * u * n⁻¹ = u⁻¹ → ∀ w ∈ Subgroup.zpowers u, n * w * n⁻¹ = w⁻¹ := by
    rintro n u hnu _ ⟨k, rfl⟩
    change n * u ^ k * n⁻¹ = (u ^ k)⁻¹
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hnu, inv_zpow]
  have hpow_fix : ∀ (n u : G), n * u * n⁻¹ = u → ∀ w ∈ Subgroup.zpowers u, n * w * n⁻¹ = w := by
    rintro n u hnu _ ⟨k, rfl⟩
    change n * u ^ k * n⁻¹ = u ^ k
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hnu]
  have ht₂t₁ : t₂ ∉ Subgroup.zpowers t₁ := by
    intro h
    have := hpow_inv j₁ t₁ h₁₁ t₂ h
    rw [h₁₂] at this
    exact hinv_ne t₂ ht₂o this.symm
  have hBJ12 : Bs ⊓ J = Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ :=
    eq_sup_zpowers_of_card Nat.prime_five hBJE (by rw [hBJ25]; norm_num) ht₁ ht₁1 ht₂ ht₂t₁
  have hconj_C : ∀ (n u : G), n * u * n⁻¹ = u → u ∈ Subgroup.centralizer ({n} : Set G) := by
    intro n u h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * n = n * u * n⁻¹ * n := by rw [h]
      _ = n * u := by group
  have hC_conj : ∀ (n u : G), u ∈ Subgroup.centralizer ({n} : Set G) → n * u * n⁻¹ = u := by
    intro n u h
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    rw [← h]
    group
  have hsq_fix : ∀ (n u : G), n * u * n⁻¹ = u⁻¹ → n ^ 2 * u * (n ^ 2)⁻¹ = u := by
    intro n u h
    calc n ^ 2 * u * (n ^ 2)⁻¹ = n * (n * u * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      _ = n * u⁻¹ * n⁻¹ := by rw [h]
      _ = (n * u * n⁻¹)⁻¹ := by group
      _ = u := by rw [h, inv_inv]
  have hsq_fix' : ∀ (n u : G), n * u * n⁻¹ = u → n ^ 2 * u * (n ^ 2)⁻¹ = u := by
    intro n u h
    calc n ^ 2 * u * (n ^ 2)⁻¹ = n * (n * u * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      _ = u := by rw [h, h]
  have hBs4 : Bs = (Subgroup.zpowers x ⊔ Subgroup.zpowers (a : G)) ⊔
      (Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂) := by
    rw [hBsDJ, hDxa, hBJ12]
  have hBJBs : Bs ⊓ J ≤ Bs := inf_le_left
  have hBJL : Bs ⊓ J ≤ Bs ⊓ L := inf_le_inf_left _ hJL
  have hle_C : ∀ (n : G), n * x * n⁻¹ = x → n * (a : G) * n⁻¹ = a → n * t₁ * n⁻¹ = t₁ →
      n * t₂ * n⁻¹ = t₂ → Bs ≤ Subgroup.centralizer ({n} : Set G) := by
    intro n hx ha h1 h2
    rw [hBs4]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr (hconj_C n x hx))
      (Subgroup.zpowers_le.mpr (hconj_C n _ ha))) (sup_le (Subgroup.zpowers_le.mpr (hconj_C n _ h1))
      (Subgroup.zpowers_le.mpr (hconj_C n _ h2)))
  set c : MulAut ↥Bs := ggConjAut Bs htN with hc_def
  set r₁ : MulAut ↥Bs := ggConjAut Bs hj₁ with hr₁_def
  set r₂ : MulAut ↥Bs := ggConjAut Bs hj₂ with hr₂_def
  set gS : MulAut ↥Bs := ggConjAut Bs hs with hgS_def
  set gφ : MulAut ↥Bs := ggConjAut Bs hgN with hgφ_def
  set n : G := g * j₁ * j₂ with hn_def
  have hnN : n ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hj₁) hj₂
  set d : MulAut ↥Bs := ggConjAut Bs hnN with hd_def
  have happ : ∀ {m : G} (hm : m ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs),
      ((ggConjAut Bs hm b : ↥Bs) : G) = m * b * m⁻¹ := fun hm b => ggConjAut_apply Bs hm b
  have hc_app : ∀ b : ↥Bs, ((c b : ↥Bs) : G) = t * b * t⁻¹ := fun b => ggConjAut_apply Bs htN b
  have hr₁_app : ∀ b : ↥Bs, ((r₁ b : ↥Bs) : G) = j₁ * b * j₁⁻¹ :=
    fun b => ggConjAut_apply Bs hj₁ b
  have hr₂_app : ∀ b : ↥Bs, ((r₂ b : ↥Bs) : G) = j₂ * b * j₂⁻¹ :=
    fun b => ggConjAut_apply Bs hj₂ b
  have hgS_app : ∀ b : ↥Bs, ((gS b : ↥Bs) : G) = s * b * s⁻¹ := fun b => ggConjAut_apply Bs hs b
  have hgφ_app : ∀ b : ↥Bs, ((gφ b : ↥Bs) : G) = g * b * g⁻¹ :=
    fun b => ggConjAut_apply Bs hgN b
  have hd_app : ∀ b : ↥Bs, ((d b : ↥Bs) : G) = n * b * n⁻¹ := fun b => ggConjAut_apply Bs hnN b
  have hd_eq : d = gφ * r₁ * r₂ := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.mul_apply, hd_app, hgφ_app, hr₁_app, hr₂_app, hn_def]
    group
  have hconjAut_comm : ∀ {n m : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G))
      (hm : m ∈ Subgroup.normalizer (Bs : Set G)), n * m = m * n →
      ggConjAut Bs hn * ggConjAut Bs hm = ggConjAut Bs hm * ggConjAut Bs hn := by
    intro n m hn hm h
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.mul_apply, happ, happ, happ, happ]
    calc n * (m * (b : G) * m⁻¹) * n⁻¹ = (n * m) * b * (n * m)⁻¹ := by group
      _ = (m * n) * b * (m * n)⁻¹ := by rw [h]
      _ = m * (n * b * n⁻¹) * m⁻¹ := by group
  set A : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs with hA_def
  have hALA : ggAutomizer L Bs ≤ A := le_sup_left
  have hAKA : ggAutomizer K Bs ≤ A := le_sup_right
  have hcA : c ∈ A := hAKA htA
  have hr₁A : r₁ ∈ A := hAKA (ggConjAut_mem_ggAutomizer (hJK hj₁J) hj₁)
  have hr₂A : r₂ ∈ A := hAKA (ggConjAut_mem_ggAutomizer (hJK hj₂J) hj₂)
  have hgSA : gS ∈ A := hAKA (ggConjAut_mem_ggAutomizer hsK hs)
  have hgφA : gφ ∈ A := hALA (ggConjAut_mem_ggAutomizer hgL hgN)
  have hdA : d ∈ A := hd_eq ▸ A.mul_mem (A.mul_mem hgφA hr₁A) hr₂A
  obtain ⟨e, he⟩ := hF4
  have hP : GGCoxeterPres 5 A CoxeterMatrix.F₄ e :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _,
      (ggCoxeterMatrix_reindex_refl _).symm⟩)))), he⟩
  have hAind : A ≤ ggInduced ⊤ Bs := fun φ hφ =>
    mem_ggInduced_top_of_mem_ggAutomizer
      ((sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) :
        ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs) hφ)
  obtain ⟨cs, hcs⟩ := ggF4_exists_coxeterSystem Nat.prime_five hp2 hBsE hNT hAind hP
    ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep cs
  have hRrefl : ∀ (φ : MulAut ↥Bs) (hφ : φ ∈ A), GGIsReflection 5 φ → R.IsRefl ⟨φ, hφ⟩ :=
    fun φ hφ h => (F4Model.F4Rep.isRefl_iff hRs).2 ((hcs ⟨φ, hφ⟩).2 h)
  have hvBs : v ∈ Bs := hDBs hvD
  have haBs : (a : G) ∈ Bs := hDBs haD
  let x' : ↥Bs := ⟨x, hxBs⟩
  let y' : ↥Bs := ⟨y, hyBs⟩
  let v' : ↥Bs := ⟨v, hvBs⟩
  let a' : ↥Bs := ⟨a, haBs⟩
  let t₁' : ↥Bs := ⟨t₁, ht₁.1⟩
  have hsub_inv : ∀ (u : ↥Bs) (w : G), (w = (u : G)⁻¹) → ∀ (φ : MulAut ↥Bs),
      ((φ u : ↥Bs) : G) = w → φ u = u⁻¹ := by
    intro u w hw φ h
    apply Subtype.ext
    rw [h, hw]
    rfl
  have hsub_fix : ∀ (u : ↥Bs) (φ : MulAut ↥Bs), ((φ u : ↥Bs) : G) = u → φ u = u :=
    fun u φ h => Subtype.ext h
  have hvinv' : t * v * t⁻¹ = v⁻¹ := hvinv
  have hty' : t * y * t⁻¹ = y := hty
  have hga' : g * (a : G) * g⁻¹ = (a : G)⁻¹ := hga
  have hvy : v ∉ Subgroup.zpowers y := by
    intro h
    have := hpow_fix t y hty' v h
    rw [hvinv'] at this
    exact hinv_ne v hvo this
  have hDyv : D = Subgroup.zpowers y ⊔ Subgroup.zpowers v :=
    eq_sup_zpowers_of_card Nat.prime_five hDE hDcard hyD hy1 hvD hvy
  have hDcl_vy : D = Subgroup.closure ({v, y} : Set G) := by
    rw [closure_pair_eq_sup, sup_comm, ← hDyv]
  have hDcl_ax : D = Subgroup.closure ({(a : G), x} : Set G) := by
    rw [closure_pair_eq_sup, sup_comm, ← hDxa]
  have hr₁D : ∀ u ∈ D, j₁ * u * j₁⁻¹ = u := fun u hu => hDC u hu j₁ hj₁J
  have hr₂D : ∀ u ∈ D, j₂ * u * j₂⁻¹ = u := fun u hu => hDC u hu j₂ hj₂J
  have hcard_sup : ∀ {H : Subgroup G}, H ≤ Bs ⊓ J → Nat.card H = 5 →
      Nat.card ↥(D ⊔ H) = 125 := by
    intro H hH h5
    rw [CFSG.card_sup_eq_mul_of_commute D H
      (fun u hu w hw => hcomm u (hDBs hu) w (hH hw).1) ?_, hDcard, h5]
    · norm_num
    · rw [eq_bot_iff]
      intro u hu
      rw [← hDJbot]
      exact ⟨hu.1, (hH hu.2).2⟩
  have hz5 : ∀ {u : G}, orderOf u = 5 → Nat.card (Subgroup.zpowers u) = 5 := by
    intro u hu
    rw [Nat.card_zpowers, hu]
  have hzle : ∀ {u : G}, u ∈ Bs ⊓ J → Subgroup.zpowers u ≤ Bs ⊓ J :=
    fun hu => Subgroup.zpowers_le.mpr hu
  have hr₁2 : r₁ ^ 2 = 1 := by
    have hC := hle_C (j₁ ^ 2) (hsq_fix' j₁ x (hr₁D x hxD)) (hsq_fix' j₁ _ (hr₁D _ haD))
      (hsq_fix j₁ t₁ h₁₁) (hsq_fix' j₁ t₂ h₁₂)
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hr₁_def, ggConjAut_pow_apply, MulAut.one_apply]
    exact hC_conj _ _ (hC b.2)
  have hr₁R : GGIsReflection 5 r₁ := by
    refine ggIsReflection_five_of_le_fix hBsE hcard hr₁2
      (sup_le hDBs ((hzle ht₂).trans hBJBs)) (hcard_sup (hzle ht₂) (hz5 ht₂o)) ?_ (b₀ := t₁') ?_
    · intro b hb
      apply Subtype.ext
      rw [hr₁_app]
      have hle : D ⊔ Subgroup.zpowers t₂ ≤ Subgroup.centralizer ({j₁} : Set G) :=
        sup_le (fun u hu => hconj_C j₁ u (hr₁D u hu))
          (Subgroup.zpowers_le.mpr (hconj_C j₁ t₂ h₁₂))
      exact hC_conj _ _ (hle hb)
    · intro h
      have h' := congrArg Subtype.val h
      rw [hr₁_app] at h'
      change j₁ * t₁ * j₁⁻¹ = t₁ at h'
      rw [h₁₁] at h'
      exact hinv_ne t₁ ht₁o h'
  have hr₂_eq : r₂ = gS * r₁ * gS⁻¹ := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.mul_apply, hr₂_app, hgS_app, hr₁_app]
    have hinv : ((gS⁻¹ b : ↥Bs) : G) = s⁻¹ * b * s := by
      have h1 : gS (gS⁻¹ b) = b := by simp
      have h2 := congrArg Subtype.val h1
      rw [hgS_app] at h2
      calc ((gS⁻¹ b : ↥Bs) : G) = s⁻¹ * (s * ((gS⁻¹ b : ↥Bs) : G) * s⁻¹) * s := by group
        _ = s⁻¹ * b * s := by rw [h2]
    rw [hinv, ← hsj]
    group
  have hr₂R : GGIsReflection 5 r₂ := hr₂_eq ▸ GGIsReflection.conj' hr₁R gS
  have ht₁L : t₁ ∈ Bs ⊓ L := hBJL ht₁
  have ht₂L : t₂ ∈ Bs ⊓ L := hBJL ht₂
  have hnx : n * x * n⁻¹ = x := by
    calc n * x * n⁻¹ = g * (j₁ * (j₂ * x * j₂⁻¹) * j₁⁻¹) * g⁻¹ := by rw [hn_def]; group
      _ = x := by rw [hr₂D x hxD, hr₁D x hxD, hgx]
  have hna : n * (a : G) * n⁻¹ = (a : G)⁻¹ := by
    calc n * (a : G) * n⁻¹ = g * (j₁ * (j₂ * (a : G) * j₂⁻¹) * j₁⁻¹) * g⁻¹ := by
          rw [hn_def]; group
      _ = (a : G)⁻¹ := by rw [hr₂D _ haD, hr₁D _ haD, hga']
  have hnt₁ : n * t₁ * n⁻¹ = t₁ := by
    calc n * t₁ * n⁻¹ = g * (j₁ * (j₂ * t₁ * j₂⁻¹) * j₁⁻¹) * g⁻¹ := by rw [hn_def]; group
      _ = g * (j₁ * t₁ * j₁⁻¹) * g⁻¹ := by rw [h₂₁]
      _ = (g * t₁ * g⁻¹)⁻¹ := by rw [h₁₁]; group
      _ = t₁ := by rw [hginv t₁ ht₁L, inv_inv]
  have hnt₂ : n * t₂ * n⁻¹ = t₂ := by
    calc n * t₂ * n⁻¹ = g * (j₁ * (j₂ * t₂ * j₂⁻¹) * j₁⁻¹) * g⁻¹ := by rw [hn_def]; group
      _ = g * (j₁ * t₂ * j₁⁻¹)⁻¹ * g⁻¹ := by rw [h₂₂]; group
      _ = (g * t₂ * g⁻¹)⁻¹ := by rw [h₁₂]; group
      _ = t₂ := by rw [hginv t₂ ht₂L, inv_inv]
  have hnBJ : ∀ u ∈ Bs ⊓ J, n * u * n⁻¹ = u := by
    intro u hu
    rw [hBJ12] at hu
    have hle : Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ ≤ Subgroup.centralizer ({n} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (hconj_C n t₁ hnt₁))
        (Subgroup.zpowers_le.mpr (hconj_C n t₂ hnt₂))
    exact hC_conj n u (hle hu)
  have hd2 : d ^ 2 = 1 := by
    have hC := hle_C (n ^ 2) (hsq_fix' n x hnx) (hsq_fix n _ hna) (hsq_fix' n t₁ hnt₁)
      (hsq_fix' n t₂ hnt₂)
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hd_def, ggConjAut_pow_apply, MulAut.one_apply]
    exact hC_conj _ _ (hC b.2)
  have hxJ : Subgroup.zpowers x ⊓ (Bs ⊓ J) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [← hDJbot]
    exact ⟨Subgroup.zpowers_le.mpr hxD hu.1, hu.2.2⟩
  have hxo : orderOf x = 5 := by
    have h := hBsE.2 x hxBs
    exact orderOf_eq_prime h hx1
  have hcard_xJ : Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ J)) = 125 := by
    rw [CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers x) (Bs ⊓ J)
      (fun u hu w hw => hcomm u (Subgroup.zpowers_le.mpr hxBs hu) w hw.1) hxJ, hz5 hxo, hBJ25]
  have hdR : GGIsReflection 5 d := by
    refine ggIsReflection_five_of_le_fix hBsE hcard hd2
      (sup_le (Subgroup.zpowers_le.mpr hxBs) hBJBs) hcard_xJ ?_ (b₀ := a') ?_
    · intro b hb
      apply Subtype.ext
      rw [hd_app]
      have hle : Subgroup.zpowers x ⊔ (Bs ⊓ J) ≤ Subgroup.centralizer ({n} : Set G) :=
        sup_le (Subgroup.zpowers_le.mpr (hconj_C n x hnx)) (fun u hu => hconj_C n u (hnBJ u hu))
      exact hC_conj _ _ (hle hb)
    · intro h
      have h' := congrArg Subtype.val h
      rw [hd_app] at h'
      change n * (a : G) * n⁻¹ = a at h'
      rw [hna] at h'
      exact hinv_ne _ hao h'
  have hcR : GGIsReflection 5 c := htR
  let cA : ↥A := ⟨c, hcA⟩
  let dA : ↥A := ⟨d, hdA⟩
  let r₁A : ↥A := ⟨r₁, hr₁A⟩
  let r₂A : ↥A := ⟨r₂, hr₂A⟩
  let gSA : ↥A := ⟨gS, hgSA⟩
  have hcRf : R.IsRefl cA := hRrefl c hcA hcR
  have hdRf : R.IsRefl dA := hRrefl d hdA hdR
  have hr₁Rf : R.IsRefl r₁A := hRrefl r₁ hr₁A hr₁R
  have hr₂Rf : R.IsRefl r₂A := hRrefl r₂ hr₂A hr₂R
  have hcommA : ∀ {φ ψ : ↥A}, (φ : MulAut ↥Bs) * ψ = ψ * φ → Commute φ ψ :=
    fun h => Subtype.ext h
  have hr₁₂ : Commute r₁A r₂A := hcommA (hconjAut_comm hj₁ hj₂ hj₁₂)
  have htj : ∀ j ∈ J, t * j = j * t := fun j hj => (Subgroup.mem_centralizer_iff.mp htJ j hj).symm
  have hcr₁ : Commute cA r₁A := hcommA (hconjAut_comm htN hj₁ (htj j₁ hj₁J))
  have hcr₂ : Commute cA r₂A := hcommA (hconjAut_comm htN hj₂ (htj j₂ hj₂J))
  have hnD : ∀ u ∈ D, n * u * n⁻¹ ∈ D := by
    intro u hu
    have h : n * u * n⁻¹ = g * u * g⁻¹ := by
      calc n * u * n⁻¹ = g * (j₁ * (j₂ * u * j₂⁻¹) * j₁⁻¹) * g⁻¹ := by rw [hn_def]; group
        _ = g * u * g⁻¹ := by rw [hr₂D u hu, hr₁D u hu]
    rw [h]
    exact (Subgroup.mem_normalizer_iff.mp hgND u).mp hu
  have hjBJ : ∀ {j : G}, j ∈ J → j ∈ Subgroup.normalizer (Bs : Set G) →
      ∀ u ∈ Bs ⊓ J, j * u * j⁻¹ ∈ Bs ⊓ J := by
    intro j hjJ hjN u hu
    exact ⟨(Subgroup.mem_normalizer_iff.mp hjN u).mp hu.1,
      J.mul_mem (J.mul_mem hjJ hu.2) (J.inv_mem hjJ)⟩
  have hdr : ∀ {j : G} (hjJ : j ∈ J) (hjN : j ∈ Subgroup.normalizer (Bs : Set G)),
      d * ggConjAut Bs hjN = ggConjAut Bs hjN * d := by
    intro j hjJ hjN
    refine ggMulAut_commute_of_split hDBs hBJBs hBsDJ (fun b hb => ?_) (fun b hb => ?_)
      (fun b hb => ?_) (fun b hb => ?_)
    · rw [hd_app]
      exact hnD b hb
    · apply Subtype.ext
      rw [hd_app]
      exact hnBJ b hb
    · apply Subtype.ext
      rw [happ]
      exact hDC b hb j hjJ
    · rw [happ]
      exact hjBJ hjJ hjN b hb
  have hdr₁ : Commute dA r₁A := hcommA (hdr hj₁J hj₁)
  have hdr₂ : Commute dA r₂A := hcommA (hdr hj₂J hj₂)
  have hcv : c v' = v'⁻¹ := Subtype.ext (by rw [hc_app]; exact hvinv')
  have hcy : c y' = y' := Subtype.ext (by rw [hc_app]; exact hty')
  have hdx : d x' = x' := Subtype.ext (by rw [hd_app]; exact hnx)
  have hda : d a' = a'⁻¹ := Subtype.ext (by rw [hd_app]; exact hna)
  have hv'1 : v' ≠ v'⁻¹ := fun h => hinv_ne v hvo (congrArg Subtype.val h).symm
  have ha'1 : a' ≠ a'⁻¹ := fun h => hinv_ne _ hao (congrArg Subtype.val h).symm
  have hrD : ∀ {j : G} (hjJ : j ∈ J) (hjN : j ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs),
      (b : G) ∈ D → ggConjAut Bs hjN b = b :=
    fun hjJ hjN b hb => Subtype.ext (by rw [happ]; exact hDC b hb _ hjJ)
  have hcne : ∀ {j : G} (hjJ : j ∈ J) (hjN : j ∈ Subgroup.normalizer (Bs : Set G)),
      c ≠ ggConjAut Bs hjN := by
    intro j hjJ hjN h
    apply hv'1
    rw [← hcv, h, hrD hjJ hjN v' hvD]
  have hdne : ∀ {j : G} (hjJ : j ∈ J) (hjN : j ∈ Subgroup.normalizer (Bs : Set G)),
      d ≠ ggConjAut Bs hjN := by
    intro j hjJ hjN h
    apply ha'1
    rw [← hda, h, hrD hjJ hjN a' haD]
  have hcd : c ≠ d := by
    intro h
    have hcx : c x' = x' := by rw [h]; exact hdx
    have hcD := apply_eq_of_mem_closure_pair (s := c) (x := x') (y := y') (z := v') hcx hcy
      (by rw [← hDcl]; exact hvD)
    exact hv'1 (hcD.symm.trans hcv)
  have hneA : ∀ {φ ψ : ↥A}, (φ : MulAut ↥Bs) ≠ ψ → φ ≠ ψ := fun h e => h (congrArg Subtype.val e)
  have hr₁₂ne : r₁A ≠ r₂A := by
    refine hneA fun h => ?_
    have h1 : r₁ t₁' = r₂ t₁' := by
      have h' : r₁ = r₂ := h
      rw [h']
    have h2 := congrArg Subtype.val h1
    rw [hr₁_app, hr₂_app] at h2
    change j₁ * t₁ * j₁⁻¹ = j₂ * t₁ * j₂⁻¹ at h2
    rw [h₁₁, h₂₁] at h2
    exact hinv_ne t₁ ht₁o h2
  have hcls : R.cls r₁A = R.cls r₂A := by
    have hconj : r₂A = gSA * r₁A * gSA⁻¹ := Subtype.ext hr₂_eq
    rw [hconj, R.cls_conj hr₁Rf gSA]
  obtain ⟨hcase₁, hcase₂⟩ := R.cls_eq_or_orderOf_eq_four_of_pairFrame hr₁Rf hr₂Rf hr₁₂
    hr₁₂ne hcls hcRf hdRf hcr₁ hcr₂ hdr₁ hdr₂ (hneA (hcne hj₁J hj₁)) (hneA (hcne hj₂J hj₂))
    (hneA (hdne hj₁J hj₁)) (hneA (hdne hj₂J hj₂)) (hneA hcd)
  have hy'1 : y' ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hcInd : c ∈ ggInduced ⊤ Bs := hAind hcA
  have hdInd : d ∈ ggInduced ⊤ Bs := hAind hdA
  have hzeq : ∀ {u w : G}, orderOf u = 5 → orderOf w = 5 → u ∈ Subgroup.zpowers w →
      w ∈ Subgroup.zpowers u := by
    intro u w hu hw h
    have hle : Subgroup.zpowers u ≤ Subgroup.zpowers w := Subgroup.zpowers_le.mpr h
    have heq : Subgroup.zpowers u = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hu, hw])
    rw [heq]
    exact Subgroup.mem_zpowers w
  have hvK : v ∈ K := by
    have h1 : t * (v * t⁻¹ * v⁻¹) ∈ K :=
      K.mul_mem htK ((Subgroup.mem_normalizer_iff.mp (hBsK hvBs) t⁻¹).mp (K.inv_mem htK))
    have h2 : t * (v * t⁻¹ * v⁻¹) = v⁻¹ * v⁻¹ := by
      calc t * (v * t⁻¹ * v⁻¹) = (t * v * t⁻¹) * v⁻¹ := by group
        _ = v⁻¹ * v⁻¹ := by rw [hvinv']
    rw [h2] at h1
    have hv5 : v ^ 5 = 1 := by rw [← hvo]; exact pow_orderOf_eq_one v
    have h3 : (v⁻¹ * v⁻¹) * (v⁻¹ * v⁻¹) = v := by
      calc (v⁻¹ * v⁻¹) * (v⁻¹ * v⁻¹) = v * (v ^ 5)⁻¹ := by group
        _ = v := by rw [hv5, inv_one, mul_one]
    rw [← h3]
    exact K.mul_mem h1 h1
  have hgy_n : g * y * g⁻¹ = n * y * n⁻¹ := by
    calc g * y * g⁻¹ = g * (j₁ * (j₂ * y * j₂⁻¹) * j₁⁻¹) * g⁻¹ := by rw [hr₂D y hyD, hr₁D y hyD]
      _ = n * y * n⁻¹ := by rw [hn_def]; group
  by_cases hcom : Commute cA dA
  ·
    exfalso
    have hclsEq := hcase₁ hcom
    have hcd' : c * d = d * c := congrArg Subtype.val hcom
    have hca : c a' = a' := GGIsReflection.apply_eq_of_commute hp2 hBsE hcR hdR hcd' hcd hda
    have hdv : d v' = v' :=
      GGIsReflection.apply_eq_of_commute hp2 hBsE hdR hcR hcd'.symm (Ne.symm hcd) hcv
    have hay : (a : G) ∈ Subgroup.zpowers y :=
      mem_zpowers_of_apply_eq_of_mem_closure hp2 hBsE (t := c) (x := v') (y := y') (z := a')
        hcv hcy hca (by rw [← hDcl_vy]; exact haD)
    have hvx : v ∈ Subgroup.zpowers x :=
      mem_zpowers_of_apply_eq_of_mem_closure hp2 hBsE (t := d) (x := a') (y := x') (z := v')
        hda hdx hdv (by rw [← hDcl_ax]; exact hvD)
    have hxv : x ∈ Subgroup.zpowers v := hzeq hvo hxo hvx
    have hya : y ∈ Subgroup.zpowers (a : G) := hzeq hao hyo hay
    have hcx : c x' = x'⁻¹ := Subtype.ext (by rw [hc_app]; exact hpow_inv t v hvinv' x hxv)
    have hdy : d y' = y'⁻¹ := Subtype.ext (by rw [hd_app]; exact hpow_inv n _ hna y hya)
    have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
    have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hNbr.1.2.2.2.1
    have hLc : (ggAutomizer L Bs).subgroupOf A ≤ Subgroup.centralizer ({cA} : Set ↥A) := by
      intro φ hφ
      have hφL : (φ : MulAut ↥Bs) ∈ ggAutomizer L Bs := hφ
      have hfix := ggRC_automizer_fixes_y hxBs hLx φ hφL
      have h := GGIsReflection.commute_of_apply_eq hp2 hBsE hNT (hAind φ.2) hcInd hcR hx'1 hcx
        hfix
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext h
    have hKd : (ggAutomizer K Bs).subgroupOf A ≤ Subgroup.centralizer ({dA} : Set ↥A) := by
      intro φ hφ
      have hφK : (φ : MulAut ↥Bs) ∈ ggAutomizer K Bs := hφ
      have hfix := ggRC_automizer_fixes_y hyBs hKy φ hφK
      have h := GGIsReflection.commute_of_apply_eq hp2 hBsE hNT (hAind φ.2) hdInd hdR hy'1 hdy
        hfix
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext h
    have htop : (⊤ : Subgroup ↥A) =
        (ggAutomizer L Bs).subgroupOf A ⊔ (ggAutomizer K Bs).subgroupOf A := by
      rw [← Subgroup.subgroupOf_sup hALA hAKA]
      exact (Subgroup.subgroupOf_self A).symm
    apply R.centralizer_sup_ne_top hcRf hdRf hclsEq.symm hcom
    rw [eq_top_iff, htop]
    exact sup_le_sup hLc hKd
  ·
    have h4 := hcase₂ hcom
    have hcinv : cA⁻¹ = cA := R.inv_eq_self_of_isRefl hcRf
    have hdinv : dA⁻¹ = dA := R.inv_eq_self_of_isRefl hdRf
    have h4' : (cA * dA) ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one _
    have hcc' : cA * (dA * cA * dA⁻¹) = (dA * cA * dA⁻¹) * cA := by
      have hsq : (cA * dA) ^ 2 = ((cA * dA) ^ 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_add]
        exact h4'
      rw [hdinv]
      calc cA * (dA * cA * dA) = (cA * dA) ^ 2 := by rw [pow_two]; group
        _ = ((cA * dA) ^ 2)⁻¹ := hsq
        _ = dA⁻¹ * cA⁻¹ * dA⁻¹ * cA⁻¹ := by rw [pow_two]; group
        _ = dA * cA * dA * cA := by rw [hcinv, hdinv]
    have hcc'ne : cA ≠ dA * cA * dA⁻¹ := by
      intro h
      apply hcom
      show cA * dA = dA * cA
      calc cA * dA = dA * cA * dA⁻¹ * dA := by rw [← h]
        _ = dA * cA := by group
    have hcc'φ : c * (d * c * d⁻¹) = (d * c * d⁻¹) * c := by
      have := congrArg Subtype.val hcc'
      simpa using this
    have hc'ne : c ≠ d * c * d⁻¹ := by
      intro h
      apply hcc'ne
      apply Subtype.ext
      simpa using h
    have hc'R : GGIsReflection 5 (d * c * d⁻¹) := GGIsReflection.conj' hcR d
    have hc'dv : (d * c * d⁻¹) (d v') = (d v')⁻¹ := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, hcv, map_inv]
    have hcdv : c (d v') = d v' :=
      GGIsReflection.apply_eq_of_commute hp2 hBsE hcR hc'R hcc'φ hc'ne hc'dv
    have hdvD : ((d v' : ↥Bs) : G) ∈ D := by rw [hd_app]; exact hnD v hvD
    have hdvy : ((d v' : ↥Bs) : G) ∈ Subgroup.zpowers y :=
      mem_zpowers_of_apply_eq_of_mem_closure hp2 hBsE (t := c) (x := v') (y := y') (z := d v')
        hcv hcy hcdv (by rw [← hDcl_vy]; exact hdvD)
    rw [hd_app] at hdvy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdvy
    have hn2 : n * (n * v * n⁻¹) * n⁻¹ = v := by
      have h := congrArg Subtype.val (congrArg (fun φ : MulAut ↥Bs => φ v') hd2)
      simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at h
      rw [hd_app, hd_app] at h
      exact h
    have hvny : v ∈ Subgroup.zpowers (n * y * n⁻¹) := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← hn2, ← hk, ← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    have hnyo : orderOf (n * y * n⁻¹) = 5 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hyo]
    exact ⟨v, ⟨hvD, hvK⟩, hvo, hDyv, hgy_n ▸ hzeq hvo hnyo hvny, t, htK, htN, htJ,
      (MulAut.conj_apply t y).symm.trans hty, (MulAut.conj_apply t v).symm.trans hvinv⟩

open N2KCoordinate CFSG.SeitzReduction.LinearPilot in
theorem ggF4N2K_block_inverters
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ t₁ t₂ j₁ j₂ s : G, j₁ ∈ Subgroup.normalizer (Bs : Set G) ∧
      j₂ ∈ Subgroup.normalizer (Bs : Set G) ∧ s ∈ Subgroup.normalizer (Bs : Set G) ∧
      j₁ ∈ J ∧ j₂ ∈ J ∧ s ∈ K ∧ t₁ ∈ Bs ⊓ J ∧ t₂ ∈ Bs ⊓ J ∧ orderOf t₁ = 5 ∧
      orderOf t₂ = 5 ∧ j₁ * t₁ * j₁⁻¹ = t₁⁻¹ ∧ j₁ * t₂ * j₁⁻¹ = t₂ ∧ j₂ * t₁ * j₂⁻¹ = t₁ ∧
      j₂ * t₂ * j₂⁻¹ = t₂⁻¹ ∧ j₁ * j₂ = j₂ * j₁ ∧ s * j₁ * s⁻¹ = j₂ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ψ, rho, -, hker, -, -, -, -, -, hRange, -, hTorus, -, hJ, -⟩ :=
    ggF4N2K_originalLiteralChart_of_original_data hR hNbr hL hK
  obtain ⟨-, -, -, -, hBsy, -, -, -, -⟩ := ggF4N2K_axis_plane hR hNbr hL hK
  have hyBs : y ∈ Bs := hR.1.2.1.1 hNbr.1.2.1
  set φ : SL6F4 →* G := K.subtype.comp ψ with hφ
  have hφK : ∀ w, φ w ∈ K := fun w => (ψ w).2
  have hBsK : Bs ⊓ K = coordinateTorus.map φ := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.map_map, hTorus] at hRange
    exact hRange.symm
  have hyK : ∀ k ∈ K, k * y * k⁻¹ = y := by
    intro k hk
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hNbr.1.2.2.2.1 hk)
    rw [h]
    group
  have hnorm : ∀ w : SL6F4, coordinateTorus.map (MulAut.conj w).toMonoidHom = coordinateTorus →
      φ w ∈ Subgroup.normalizer (Bs : Set G) := by
    intro w hw
    have hle : Bs.map (MulAut.conj (φ w)).toMonoidHom ≤ Bs := by
      conv_lhs => rw [hBsy]
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [MonoidHom.map_zpowers]
        refine Subgroup.zpowers_le.mpr ?_
        change φ w * y * (φ w)⁻¹ ∈ Bs
        rw [hyK _ (hφK w)]
        exact hyBs
      · rintro _ ⟨b, hb, rfl⟩
        rw [hBsK] at hb
        obtain ⟨c, hc, rfl⟩ := hb
        have hwc : w * c * w⁻¹ ∈ coordinateTorus := by
          rw [← hw]
          exact ⟨c, hc, rfl⟩
        have hmem : φ (w * c * w⁻¹) ∈ Bs ⊓ K := by
          rw [hBsK]
          exact ⟨_, hwc, rfl⟩
        have heq : (MulAut.conj (φ w)).toMonoidHom (φ c) = φ (w * c * w⁻¹) := by
          simp [MulAut.conj_apply]
        rw [heq]
        exact hmem.1
    have hcard : Nat.card (Bs.map (MulAut.conj (φ w)).toMonoidHom) = Nat.card Bs :=
      Subgroup.card_map_of_injective (MulAut.conj (φ w)).injective
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))
  obtain ⟨w₂, hw₂⟩ := CFSG.RankThree.PartOne.KF132.exists_inv_conj_sl2 coordA2
  have hm01 : ∀ A : SL2F4, coordBlock01 A ∈ blockSpecialLinear coordJ01 := fun A => by
    rw [← range_pairEmbed (K := F4) (a := (0 : Fin 6)) (b := (1 : Fin 6)) (by decide)]
    exact ⟨A, rfl⟩
  have hm23 : ∀ A : SL2F4, coordBlock23 A ∈ blockSpecialLinear coordJ23 := fun A => by
    rw [← range_pairEmbed (K := F4) (a := (2 : Fin 6)) (b := (3 : Fin 6)) (by decide)]
    exact ⟨A, rfl⟩
  have hm45 : ∀ A : SL2F4, coordBlock45 A ∈ blockSpecialLinear coordJ45 := fun A => by
    rw [← range_pairEmbed (K := F4) (a := (4 : Fin 6)) (b := (5 : Fin 6)) (by decide)]
    exact ⟨A, rfl⟩
  have hc0123 : ∀ A B : SL2F4, Commute (coordBlock01 A) (coordBlock23 B) := fun A B =>
    commute_blockSpecialLinear_of_disjoint (by decide) (hm01 A) (hm23 B)
  have hc0145 : ∀ A B : SL2F4, Commute (coordBlock01 A) (coordBlock45 B) := fun A B =>
    commute_blockSpecialLinear_of_disjoint (by decide) (hm01 A) (hm45 B)
  have hc2345 : ∀ A B : SL2F4, Commute (coordBlock23 A) (coordBlock45 B) := fun A B =>
    commute_blockSpecialLinear_of_disjoint (by decide) (hm23 A) (hm45 B)
  have hconj_fix : ∀ {w u : SL6F4}, Commute w u → (MulAut.conj w) u = u := by
    intro w u h
    rw [MulAut.conj_apply, h.eq, mul_inv_cancel_right]
  have hinv01 : (MulAut.conj (coordBlock01 w₂)) (coordBlock01 coordA2) =
      (coordBlock01 coordA2)⁻¹ := by
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hw₂, map_inv]
  have hinv23 : (MulAut.conj (coordBlock23 w₂)) (coordBlock23 coordA2) =
      (coordBlock23 coordA2)⁻¹ := by
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hw₂, map_inv]
  have hmapfix : ∀ (w u : SL6F4), (MulAut.conj w) u = u →
      (Subgroup.zpowers u).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers u := by
    intro w u h
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers h
  have hmapinv : ∀ (w u : SL6F4), (MulAut.conj w) u = u⁻¹ →
      (Subgroup.zpowers u).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers u := by
    intro w u h
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj w) u) = _
    rw [h, Subgroup.zpowers_inv]
  have hT01 : coordinateTorus.map (MulAut.conj (coordBlock01 w₂)).toMonoidHom = coordinateTorus := by
    rw [coordinateTorus, Subgroup.map_sup, Subgroup.map_sup, hmapinv _ _ hinv01,
      hmapfix _ _ (hconj_fix (hc0123 w₂ coordA2)), hmapfix _ _ (hconj_fix (hc0145 w₂ coordA2))]
  have hT23 : coordinateTorus.map (MulAut.conj (coordBlock23 w₂)).toMonoidHom = coordinateTorus := by
    rw [coordinateTorus, Subgroup.map_sup, Subgroup.map_sup,
      hmapfix _ _ (hconj_fix (hc0123 coordA2 w₂).symm), hmapinv _ _ hinv23,
      hmapfix _ _ (hconj_fix (hc2345 w₂ coordA2))]
  set σ : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 3 with hσ_def
  have hσ : σ⁻¹ = σ := by decide
  set s₀ : SL6F4 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.signedPermutation 6 F4 σ
    with hs₀
  have hpe : ∀ {a b a' b' : Fin 6} (hab : a ≠ b) (ha : a = a') (hb : b = b') (A : SL2F4),
      pairEmbed (K := F4) hab A = pairEmbed (K := F4) (ha ▸ hb ▸ hab) A := by
    rintro a b a' b' hab rfl rfl A
    rfl
  have hσ01 : ∀ A : SL2F4, (MulAut.conj s₀) (coordBlock01 A) = coordBlock23 A := by
    intro A
    have h := signedPermutation_conj_pairEmbed σ hσ (by decide : (0 : Fin 6) ≠ 1) A
    rw [hpe _ (show σ 0 = 2 by decide) (show σ 1 = 3 by decide)] at h
    exact h
  have hσ23 : ∀ A : SL2F4, (MulAut.conj s₀) (coordBlock23 A) = coordBlock01 A := by
    intro A
    have h := signedPermutation_conj_pairEmbed σ hσ (by decide : (2 : Fin 6) ≠ 3) A
    rw [hpe _ (show σ 2 = 0 by decide) (show σ 3 = 1 by decide)] at h
    exact h
  have hσ45 : ∀ A : SL2F4, (MulAut.conj s₀) (coordBlock45 A) = coordBlock45 A := by
    intro A
    have h := signedPermutation_conj_pairEmbed σ hσ (by decide : (4 : Fin 6) ≠ 5) A
    rw [hpe _ (show σ 4 = 4 by decide) (show σ 5 = 5 by decide)] at h
    exact h
  have hTσ : coordinateTorus.map (MulAut.conj s₀).toMonoidHom = coordinateTorus := by
    have h01 : coordT01.map (MulAut.conj s₀).toMonoidHom = coordT23 := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers (hσ01 coordA2)
    have h23 : coordT23.map (MulAut.conj s₀).toMonoidHom = coordT01 := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers (hσ23 coordA2)
    rw [coordinateTorus, Subgroup.map_sup, Subgroup.map_sup, h01, h23,
      hmapfix _ _ (hσ45 coordA2), sup_left_comm]
  have hfour : (CFSG.SeitzReduction.E6Pilot.blockFour (K := F4)).range =
      blockSpecialLinear ({0, 1, 2, 3} : Finset (Fin 6)) := by
    rw [ggBlockFour_eq_blockSL]
    exact ggBlockSL_range_eq_blockSpecialLinear _ _ (by decide)
  have hf01 : ∀ A : SL2F4, coordBlock01 A ∈ (CFSG.SeitzReduction.E6Pilot.blockFour (K := F4)).range :=
    fun A => hfour ▸ blockSpecialLinear_mono (by decide) (hm01 A)
  have hf23 : ∀ A : SL2F4, coordBlock23 A ∈ (CFSG.SeitzReduction.E6Pilot.blockFour (K := F4)).range :=
    fun A => hfour ▸ blockSpecialLinear_mono (by decide) (hm23 A)
  have hφJ : ∀ {w : SL6F4}, w ∈ (CFSG.SeitzReduction.E6Pilot.blockFour (K := F4)).range → φ w ∈ J := by
    intro w hw
    rw [hJ]
    exact ⟨w, hw, rfl⟩
  have hφT : ∀ {c : SL6F4}, c ∈ coordinateTorus → φ c ∈ Bs := by
    intro c hc
    have h : φ c ∈ Bs ⊓ K := by
      rw [hBsK]
      exact ⟨c, hc, rfl⟩
    exact h.1
  have hφconj : ∀ w u : SL6F4, φ w * φ u * (φ w)⁻¹ = φ ((MulAut.conj w) u) := by
    intro w u
    simp [MulAut.conj_apply]
  have hord : ∀ {c : SL6F4}, orderOf c = 5 → (∃ w : SL6F4, (MulAut.conj w) c = c⁻¹) →
      orderOf (φ c) = 5 := by
    intro c hc ⟨w, hwc⟩
    refine orderOf_eq_prime (by rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]) ?_
    intro h1
    have hcK : c ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact h1
    have hcZ := hker hcK
    have hcomm : (MulAut.conj w) c = c := by
      rw [MulAut.conj_apply, (Subgroup.mem_center_iff.mp hcZ) w, mul_inv_cancel_right]
    rw [hcomm] at hwc
    have h2 : c ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hwc]
      exact inv_mul_cancel c
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [hc] at hdvd
    norm_num at hdvd
  have hT01mem : coordBlock01 coordA2 ∈ coordinateTorus :=
    le_sup_left (a := coordT01) (Subgroup.mem_zpowers _)
  have hT23mem : coordBlock23 coordA2 ∈ coordinateTorus :=
    (le_sup_left (a := coordT23) |>.trans (le_sup_right (a := coordT01)))
      (Subgroup.mem_zpowers _)
  refine ⟨φ (coordBlock01 coordA2), φ (coordBlock23 coordA2), φ (coordBlock01 w₂),
    φ (coordBlock23 w₂), φ s₀, hnorm _ hT01, hnorm _ hT23, hnorm _ hTσ, hφJ (hf01 w₂),
    hφJ (hf23 w₂), hφK s₀, ⟨hφT hT01mem, hφJ (hf01 coordA2)⟩,
    ⟨hφT hT23mem, hφJ (hf23 coordA2)⟩,
    hord coordBlock01_order ⟨_, hinv01⟩, hord coordBlock23_order ⟨_, hinv23⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφconj, hinv01, map_inv]
  · rw [hφconj, hconj_fix (hc0123 w₂ coordA2)]
  · rw [hφconj, hconj_fix (hc0123 coordA2 w₂).symm]
  · rw [hφconj, hinv23, map_inv]
  · rw [← map_mul, ← map_mul, (hc0123 w₂ w₂).eq]
  · rw [hφconj, hσ01]

theorem ggF4N2_swap_exchanges_axes
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hginv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hgx : g * x * g⁻¹ = x) :
    ∃ v : G, v ∈ D ⊓ K ∧ orderOf v = 5 ∧ D = Subgroup.zpowers y ⊔ Subgroup.zpowers v ∧
      g * y * g⁻¹ ∈ Subgroup.zpowers v ∧
      ∃ t ∈ K, t ∈ Subgroup.normalizer (Bs : Set G) ∧ t ∈ Subgroup.centralizer (J : Set G) ∧
        t * y * t⁻¹ = y ∧ t * v * t⁻¹ = v⁻¹ := by
  obtain ⟨t₁, t₂, j₁, j₂, s, hj₁, hj₂, hs, hj₁J, hj₂J, hsK, ht₁, ht₂, ht₁o, ht₂o, h₁₁, h₁₂, h₂₁,
    h₂₂, hj₁₂, hsj⟩ := ggF4N2K_block_inverters hR hNbr hL hK
  exact ggF4N2_swap_exchanges_axes_of_inverters hR hNbr hL hK hF4 hgL hgN hginv hgx hj₁ hj₂ hs hj₁J
    hj₂J hsK ht₁ ht₂ ht₁o ht₂o h₁₁ h₁₂ h₂₁ h₂₂ hj₁₂ hsj

open CFSG.ClassicalInvolution.WeakCT in
theorem ggF4N2_mixed_charts_cross
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hginv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hgx : g * x * g⁻¹ = x)
    {ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G}
    (h₁ : ψ₁.ker ≤ Subgroup.center _) (hK₁ : ψ₁.range = K)
    (hJ₁ : (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J)
    (h₂ : ψ₂.ker ≤ Subgroup.center _) (hK₂ : ψ₂.range = K.map (MulAut.conj g).toMonoidHom)
    (hblock : ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
      ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))) :
    ∃ v : G, v ∈ D ⊓ K ∧ orderOf v = 5 ∧ D = Subgroup.zpowers y ⊔ Subgroup.zpowers v ∧
      g * y * g⁻¹ ∈ Subgroup.zpowers v ∧
      v ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁ ∧
      y ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂ := by
  obtain ⟨v, ⟨hvD, hvK⟩, hvo, hDyv, hgy, -⟩ :=
    ggF4N2_swap_exchanges_axes hR hNbr hL hK hF4 hgL hgN hginv hgx
  obtain ⟨-, -, hyo, hDcl, -, -⟩ := ggF4N2_x_data hR hNbr
  have hyD : y ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hDeq : D = Bs ⊓ Subgroup.centralizer (J : Set G) := ggF4N2_D_eq_Bs_inf_centralizer_J hR hL
  have hDC : ∀ d ∈ D, d ∈ Subgroup.centralizer (J : Set G) := fun d hd =>
    (hDeq ▸ hd : d ∈ Bs ⊓ _).2
  have h30 : (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range ≤
      (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)).range := by
    rw [ggBlockSL_range_eq_blockSpecialLinear _ ({0, 1, 2} : Finset (Fin 6)) (by decide),
      ggBlockSL_range_eq_blockSpecialLinear _ ({0, 1, 2, 3} : Finset (Fin 6)) (by decide)]
    exact CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_mono (by decide)
  have hC : ∀ ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G,
      (ψ.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J → ∀ d ∈ D,
      d ∈ Subgroup.centralizer
        (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G) := by
    intro ψ hψ d hd
    have hMJ : (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ ≤ J := by
      rw [← hψ, MonoidHom.range_comp]
      exact Subgroup.map_mono h30
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hMJ) (hDC d hd)
  have hJ₂ : (ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J := by
    rw [hblock, hJ₁]
  have hDle : D ≤ Subgroup.centralizer ({g ^ 2} : Set G) :=
    ggF4N2L_swap_sq_centralizes hR hL hgL hginv hgx
  have hyKg : y ∈ ψ₂.range := by
    rw [hK₂]
    have h2 : y * g ^ 2 = g ^ 2 * y := Subgroup.mem_centralizer_singleton_iff.mp (hDle hyD)
    rw [pow_two] at h2
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · have h : g⁻¹ * y * g = g * y * g⁻¹ := by
        calc g⁻¹ * y * g = g⁻¹ * (y * (g * g)) * g⁻¹ := by group
          _ = g⁻¹ * (g * g * y) * g⁻¹ := by rw [h2]
          _ = g * y * g⁻¹ := by group
      rw [h]
      exact (Subgroup.zpowers_le.mpr hvK) hgy
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  refine ⟨v, ⟨hvD, hvK⟩, hvo, hDyv, hgy, ?_, ?_⟩
  · refine ggSL6Chart_mem_complement_of_mem_centralizer ψ₁ h₁ (by rw [hK₁]; exact hvK) ?_
      (hC ψ₁ hJ₁ v hvD)
    rw [← hvo]
    exact pow_orderOf_eq_one v
  · refine ggSL6Chart_mem_complement_of_mem_centralizer ψ₂ h₂ hyKg ?_ (hC ψ₂ hJ₂ y hyD)
    rw [← hyo]
    exact pow_orderOf_eq_one y

end Alignment

end CFSG.StandardType
