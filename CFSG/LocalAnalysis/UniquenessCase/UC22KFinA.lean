module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sl
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xb
import CFSG.RankThree.PartOne.KFCL.L4Block
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob
import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement Pointwise
open P22sj P22s

namespace P22kA

variable {G : Type} [Group G] [Finite G] {S L V : Subgroup G} {F : Type} [Field F] [Fintype F]

theorem coe_slEquiv (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((slEquiv F A : ↥(CFSG.Open.StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) := by
  have h := coe_slEquiv_symm F (slEquiv F A)
  rw [MulEquiv.symm_apply_apply] at h
  exact h.symm

theorem uc22k_lside {e : ℕ} (hF : Fintype.card F = 2 ^ e) (he : 2 ≤ e)
    (hS2 : IsPGroup 2 S) (hSL : S ≤ normalizer (L : Set G)) (hSV : S ≤ normalizer (V : Set G))
    (hLV : L ≤ normalizer (V : Set G)) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hLp : ⁅L, L⁆ = L)
    (hLq : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf S (L ⊔ S))
    (α : ↥L →* ↥(CFSG.Open.StatedSL 2 F)) (hα : Function.Surjective α)
    (hαk : α.ker = (L ⊓ centralizer (V : Set G)).subgroupOf L)
    (β : ↥⁅V, L⁆ →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβk : β.ker = (⁅V, L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (hβα : ∀ (l : ↥L) (u v : ↥⁅V, L⁆), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β v) = (((α l : ↥(CFSG.Open.StatedSL 2 F)) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hinn : ∀ b ∈ S, ∃ l ∈ L, ∀ u v : ↥⁅V, L⁆, (v : G) = (l⁻¹ * b) * u * (l⁻¹ * b)⁻¹ → β v = β u) :
    CFSG.Open.pCoreOf 2 (L ⊔ S) ≤ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ∧
      S ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ CFSG.Open.pCoreOf 2 (L ⊔ S) ∧
      ∀ T A : Subgroup G, ⁅V, L⁆ ≤ T → CFSG.Open.IsElemAbelian 2 ⁅V, L⁆ →
        CFSG.Quasithin.IsMaxElemAbelian T A → A ≤ S →
        CFSG.Quasithin.IsMaxElemAbelian T ((A ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G)) ⊔ ⁅V, L⁆) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchp : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hF' : Nat.card F = 2 ^ e := by rw [Nat.card_eq_fintype_card, hF]
  have h4 : 4 ≤ Nat.card F := by
    rw [hF']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  haveI hsimpleSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup h4
  set H : Subgroup G := L ⊔ S with hHdef
  have hLH : L ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  have hHL : H ≤ normalizer (L : Set G) := sup_le le_normalizer hSL
  have hHV : H ≤ normalizer (V : Set G) := sup_le hLV hSV
  have hHW₁ : H ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun h hh =>
    CFSG.Quasithin.SBd5.mem_normalizer_commutator_of (hHV hh) (hHL hh)
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  set α' : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F := (slEquiv F).symm.toMonoidHom.comp α with hα'def
  have hα' : Function.Surjective α' := (slEquiv F).symm.surjective.comp hα
  have hβα' : ∀ (l : ↥L) (u v : ↥⁅V, L⁆), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β v) = (α' l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)) := by
    intro l u v h
    rw [hβα l u v h, hα'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_slEquiv_symm]
  have hHW01 : ∀ g ∈ H, ∀ w ∈ ⁅V, L⁆ ⊓ centralizer (L : Set G), g * w * g⁻¹ ∈ ⁅V, L⁆ ⊓ centralizer (L : Set G) :=
    fun g hg w hw => ⟨(Subgroup.mem_normalizer_iff.mp (hHW₁ hg) w).mp hw.1,
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (hHL hg)) w).mp hw.2⟩
  have hcongr : ∀ (g : ↥H) (u v : ↥⁅V, L⁆), β u = β v → β (act hHW₁ g u) = β (act hHW₁ g v) := by
    intro g u v huv
    have h1 : u⁻¹ * v ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
    rw [hβk, mem_subgroupOf] at h1
    have h2 : (act hHW₁ g u)⁻¹ * (act hHW₁ g v) ∈ β.ker := by
      rw [hβk, mem_subgroupOf]
      have e : (act hHW₁ g u)⁻¹ * (act hHW₁ g v) = act hHW₁ g (u⁻¹ * v) := by
        simp [map_mul, map_inv]
      rw [e, act_coe hHW₁ g (u⁻¹ * v)]
      exact hHW01 g g.2 _ h1
    rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
    exact inv_mul_eq_one.mp h2
  obtain ⟨ρ, -, hact⟩ := CFSG.Quasithin.exists_perm_action (act hHW₁) β hβ hcongr
  have hρL : ∀ l : ↥L, ρ ⟨(l : G), hLH l.2⟩ = slPerm F (α' l) := by
    intro l
    refine Equiv.ext fun x => ?_
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd x)
    have hux : Multiplicative.toAdd (β u) = x := by rw [hu]; rfl
    rw [← hux, hact, slPerm_apply, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    exact hβα' l u _ (act_coe hHW₁ _ u)
  have hρS : ∀ s : ↥H, (s : G) ∈ S → ∃ l : ↥L, ρ s = slPerm F (α' l) := by
    intro s hs
    obtain ⟨l, hl, hls⟩ := hinn (s : G) hs
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [← hρL]
    have h1 : ρ ((⟨l, hLH hl⟩ : ↥H)⁻¹ * s) = 1 := by
      refine Equiv.ext fun x => ?_
      obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd x)
      have hux : Multiplicative.toAdd (β u) = x := by rw [hu]; rfl
      rw [← hux, hact, Equiv.Perm.one_apply]
      congr 1
      refine hls u _ ?_
      rw [act_coe]
      simp
    have h2 : s = (⟨l, hLH hl⟩ : ↥H) * ((⟨l, hLH hl⟩ : ↥H)⁻¹ * s) := by group
    rw [h2, map_mul, h1, mul_one]
  have hslinj : Function.Injective (slPerm F) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    exact eq_one_of_forall_smul_vec fun w => by
      have := congrArg (fun g : Equiv.Perm (Fin 2 → F) => g w) hA
      simpa [slPerm_apply] using this
  set L' : Subgroup ↥H := L.subgroupOf H with hL'def
  set S' : Subgroup ↥H := S.subgroupOf H with hS'def
  have htop : L' ⊔ S' = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLH, Subgroup.map_subgroupOf_eq_of_le hSH,
      Subgroup.map_top, Subgroup.range_subtype]
  have hrange : ∀ h : ↥H, ρ h ∈ (slPerm F).range := by
    let P : Subgroup ↥H := (slPerm F).range.comap ρ
    have hLP : L' ≤ P := fun h hh => ⟨α' ⟨(h : G), hh⟩, (hρL ⟨(h : G), hh⟩).symm⟩
    have hSP : S' ≤ P := fun h hh => by
      obtain ⟨l, hl⟩ := hρS h hh
      exact ⟨α' l, hl.symm⟩
    intro h
    have : h ∈ P := (sup_le hLP hSP) (htop ▸ Subgroup.mem_top h)
    exact this
  let eSL : Matrix.SpecialLinearGroup (Fin 2) F ≃* (slPerm F).range := MonoidHom.ofInjective hslinj
  let φ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) F :=
    eSL.symm.toMonoidHom.comp (ρ.codRestrict (slPerm F).range hrange)
  have hφρ : ∀ h : ↥H, slPerm F (φ h) = ρ h := by
    intro h
    have h1 : eSL (φ h) = ρ.codRestrict (slPerm F).range hrange h := by
      show eSL (eSL.symm _) = _
      rw [MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hφL : ∀ l : ↥L, φ ⟨(l : G), hLH l.2⟩ = α' l := fun l => hslinj ((hφρ _).trans (hρL l))
  have hφs : Function.Surjective φ := by
    intro A
    obtain ⟨l, rfl⟩ := hα' A
    exact ⟨_, hφL l⟩
  have hφact : ∀ (h : ↥H) (u : ↥⁅V, L⁆), Multiplicative.toAdd (β (act hHW₁ h u)) =
      (φ h : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)) := by
    intro h u
    rw [← hact, ← hφρ, slPerm_apply, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  have htriv : ∀ h : ↥H, φ h = 1 → (h : G) ∈ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    intro h hh
    refine mem_centralizer_of_trivial α hαk β hβ hβk hβα hV hLV hLp (hHL h.2) (hHV h.2) fun u v huv => ?_
    have hv : act hHW₁ h u = v := Subtype.ext (by rw [act_coe]; exact huv.symm)
    have h1 := hφact h u
    rw [hh, hv] at h1
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h1
    exact Multiplicative.toAdd.injective h1
  have hfix : ∀ h : ↥H, (h : G) ∈ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) → φ h = 1 := by
    intro h hh
    refine eq_one_of_forall_smul_vec fun x => ?_
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd x)
    have hux : Multiplicative.toAdd (β u) = x := by rw [hu]; rfl
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, ← hux, ← hφact]
    congr 2
    apply Subtype.ext
    rw [act_coe]
    have := Subgroup.mem_centralizer_iff.1 hh (u : G) u.2
    rw [← this]
    group
  have hO1 : CFSG.Open.pCoreOf 2 H ≤ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    refine htriv y ?_
    haveI hn : ((CFSG.pCore 2 ↥H).map φ).Normal := Subgroup.Normal.map inferInstance φ hφs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥H).map φ) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).1 hb hy
    · exfalso
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥H).map φ) := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map φ
      rw [ht] at hp
      exact not_isPGroup_sl2 hF he (hp.of_equiv Subgroup.topEquiv)
  haveI hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHL
  have hS'2 : IsPGroup 2 S' := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  set Q' : Subgroup ↥H := (CFSG.pCore 2 ↥L).map (Subgroup.inclusion hLH) with hQ'def
  have hQ'2 : IsPGroup 2 Q' := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map _
  have hQ'mem : ∀ x : ↥H, (x : G) ∈ CFSG.Open.pCoreOf 2 L → x ∈ Q' := by
    rintro x ⟨q, hq, hqx⟩
    exact ⟨q, hq, Subtype.ext hqx⟩
  haveI hQ'n : Q'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hn
    have hgN := UC6S846.normalizer_le_normalizer_pCoreOf L (hHL g.2)
    have h1 : (g : G) * ((q : ↥L) : G) * (g : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
      (mem_normalizer_iff.mp hgN _).mp ⟨q, hq, rfl⟩
    exact hQ'mem _ h1
  have hQ'H : Q' ≤ CFSG.pCore 2 ↥H := CFSG.LieType.BorelTits.le_pCore 2 hQ'n hQ'2
  have hQα : CFSG.pCore 2 ↥L ≤ α'.ker := by
    haveI hn : ((CFSG.pCore 2 ↥L).map α').Normal := Subgroup.Normal.map inferInstance α' hα'
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥L).map α') with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).1 hb
    · exfalso
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥L).map α') := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map α'
      rw [ht] at hp
      exact not_isPGroup_sl2 hF he (hp.of_equiv Subgroup.topEquiv)
  have hcent : ∀ z : ↥L, α' z = 1 →
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) z ∈ center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro z hz
    have hNn : (α'.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    have hNne : α'.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≠ ⊤ := by
      intro hN
      have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) hN
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hQα, Subgroup.comap_top] at h1
      obtain ⟨A, hA⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) F)
      obtain ⟨l, rfl⟩ := hα' A
      exact hA (MonoidHom.mem_ker.1 (h1 ▸ Subgroup.mem_top l))
    exact le_center_of_quasisimple hLq hNn hNne ⟨z, MonoidHom.mem_ker.2 hz, rfl⟩
  have hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hLp]
  have hcommQ : ∀ k ∈ φ.ker, ∀ l ∈ L', k * l * k⁻¹ * l⁻¹ ∈ Q' := by
    intro k hk lH hlH
    have hcL : ∀ l : ↥L, ((k * ⟨(l : G), hLH l.2⟩ * k⁻¹ * (⟨(l : G), hLH l.2⟩ : ↥H)⁻¹ : ↥H) : G) ∈ L := by
      intro l
      have h1 : k * ⟨(l : G), hLH l.2⟩ * k⁻¹ ∈ L' := hL'n.conj_mem _ l.2 k
      exact L'.mul_mem h1 (L'.inv_mem l.2)
    let c : ↥L → ↥L := fun l => ⟨_, hcL l⟩
    have hcα : ∀ l, α' (c l) = 1 := by
      intro l
      rw [← hφL (c l)]
      have e1 : (⟨((c l : ↥L) : G), hLH (c l).2⟩ : ↥H) =
          k * ⟨(l : G), hLH l.2⟩ * k⁻¹ * (⟨(l : G), hLH l.2⟩ : ↥H)⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.1 hk]
      group
    set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπdef
    have hcmul : ∀ l₁ l₂ : ↥L, c (l₁ * l₂) = c l₁ * (l₁ * c l₂ * l₁⁻¹) := by
      intro l₁ l₂
      apply Subtype.ext
      show (k : G) * ((l₁ : G) * l₂) * (k : G)⁻¹ * ((l₁ : G) * l₂)⁻¹ =
        ((k : G) * l₁ * (k : G)⁻¹ * (l₁ : G)⁻¹) * ((l₁ : G) * ((k : G) * l₂ * (k : G)⁻¹ * (l₂ : G)⁻¹) *
          (l₁ : G)⁻¹)
      group
    let f : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) :=
      { toFun := fun l => π (c l)
        map_one' := by
          show π (c 1) = 1
          have : c 1 = 1 := Subtype.ext (by
            show (k : G) * ((1 : ↥L) : G) * (k : G)⁻¹ * ((1 : ↥L) : G)⁻¹ = ((1 : ↥L) : G)
            simp)
          rw [this, map_one]
        map_mul' := fun l₁ l₂ => by
          show π (c (l₁ * l₂)) = π (c l₁) * π (c l₂)
          have hz := mem_center_iff.1 (hcent (c l₂) (hcα l₂))
          rw [hcmul, map_mul, map_mul, map_mul, map_inv, hz (π l₁)]
          group }
    have hfker : f.ker = ⊤ := by
      rw [eq_top_iff, ← hperf, commutator_le]
      intro x _ y _
      have hz := mem_center_iff.1 (hcent (c x) (hcα x))
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
      show π (c x) * π (c y) * (π (c x))⁻¹ * (π (c y))⁻¹ = 1
      rw [← hz (π (c y))]
      group
    have h1 : f ⟨(lH : G), hlH⟩ = 1 := MonoidHom.mem_ker.1 (hfker ▸ Subgroup.mem_top _)
    have h2 : c ⟨(lH : G), hlH⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]
      exact h1
    refine hQ'mem _ ⟨_, h2, ?_⟩
    rfl
  have hSK : S' ⊓ φ.ker ≤ CFSG.pCore 2 ↥H := by
    have hX2 : IsPGroup 2 ↥((S' ⊓ φ.ker) ⊔ Q') := (hS'2.to_inf_left).to_sup_of_normal_right hQ'2
    have hXn : ((S' ⊓ φ.ker) ⊔ Q').Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
      refine sup_le ?_ ?_
      · rw [le_normalizer_iff]
        intro l hl x hx
        rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
        obtain ⟨a, ha, q, hq, rfl⟩ := hx
        have h1 : l * a * l⁻¹ = a * (a⁻¹ * l * a⁻¹⁻¹ * l⁻¹) := by group
        have h2 : a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ ∈ Q' := hcommQ a⁻¹ (φ.ker.inv_mem ha.2) l hl
        have h3 : l * (a * q) * l⁻¹ = (a * (a⁻¹ * l * a⁻¹⁻¹ * l⁻¹)) * (l * q * l⁻¹) := by
          rw [← h1]; group
        rw [h3]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_sup_left ha) (mem_sup_right h2))
          (mem_sup_right (hQ'n.conj_mem q hq l))
      · rw [le_normalizer_iff]
        intro s hs x hx
        rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
        obtain ⟨a, ha, q, hq, rfl⟩ := hx
        have h3 : s * (a * q) * s⁻¹ = (s * a * s⁻¹) * (s * q * s⁻¹) := by group
        rw [h3]
        refine Subgroup.mul_mem _ (mem_sup_left ⟨?_, ?_⟩) (mem_sup_right (hQ'n.conj_mem q hq s))
        · exact S'.mul_mem (S'.mul_mem hs ha.1) (S'.inv_mem hs)
        · exact (inferInstance : φ.ker.Normal).conj_mem a ha.2 s
    exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCore 2 hXn hX2)
  have hO2 : S ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ CFSG.Open.pCoreOf 2 H := by
    intro s hs
    have hmem : (⟨s, hSH hs.1⟩ : ↥H) ∈ S' ⊓ φ.ker :=
      ⟨hs.1, MonoidHom.mem_ker.2 (hfix _ hs.2)⟩
    exact ⟨_, hSK hmem, rfl⟩
  refine ⟨hO1, hO2, ?_⟩
  intro T A hWT hWe hA hAS
  have hAH : A ≤ H := hAS.trans hSH
  set θ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) F := φ.comp (Subgroup.inclusion hAH) with hθdef
  have hker : θ.ker = (centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro ha
      exact htriv _ ha
    · intro ha
      exact hfix _ ha
  have hidx : (centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).relIndex A = Nat.card θ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  set B : Subgroup ↥(CFSG.Open.StatedSL 2 F) := θ.range.map (slEquiv F).toMonoidHom with hBdef
  have hB2 : IsPGroup 2 B := by
    have hA2 : IsPGroup 2 A := hS2.to_le hAS
    have hR : IsPGroup 2 θ.range := hA2.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
    exact hR.map _
  have hBcard : Nat.card B = Nat.card θ.range :=
    Subgroup.card_map_of_injective (slEquiv F).injective
  have hbound := P22x.sl2_card_mul_fix_le hF' B hB2
  set C₁ : Subgroup G := centralizer (A : Set G) ⊓ ⁅V, L⁆ with hC₁def
  set βC : ↥C₁ →* Multiplicative (Fin 2 → F) := β.comp (Subgroup.inclusion inf_le_right) with hβCdef
  have hβCfix : ∀ c : ↥C₁, Multiplicative.toAdd (βC c) ∈ P22x.sl2Fix B := by
    intro c g hg
    obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hg
    have hca : (a : G) * c * (a : G)⁻¹ = c := by
      have h0 := Subgroup.mem_centralizer_iff.1 c.2.1 (a : G) a.2
      calc (a : G) * c * (a : G)⁻¹ = c * a * (a : G)⁻¹ := by rw [h0]
        _ = c := by group
    have h1 := hφact (Subgroup.inclusion hAH a) (Subgroup.inclusion inf_le_right c)
    have h2 : act hHW₁ (Subgroup.inclusion hAH a) (Subgroup.inclusion inf_le_right c) =
        Subgroup.inclusion inf_le_right c := Subtype.ext (by rw [act_coe]; exact hca)
    rw [h2] at h1
    rw [MulEquiv.coe_toMonoidHom, coe_slEquiv]
    exact h1.symm
  have hrangeβ : Nat.card βC.range ≤ Nat.card (P22x.sl2Fix B) := by
    let j : ↥βC.range → ↥(P22x.sl2Fix B) := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (Fin 2 → F)), by
      obtain ⟨c, hc⟩ := x.2
      rw [← hc]
      exact hβCfix c⟩
    have hj : Function.Injective j := by
      intro x y hxy
      apply Subtype.ext
      have := congrArg Subtype.val hxy
      exact Multiplicative.toAdd.injective this
    exact Nat.card_le_card_of_injective j hj
  have hkerβ : Nat.card βC.ker ≤ Nat.card β.ker := by
    let j : ↥βC.ker → ↥β.ker := fun x =>
      ⟨Subgroup.inclusion inf_le_right (x : ↥C₁), by
        have hx : βC (x : ↥C₁) = 1 := x.2
        exact hx⟩
    have hj : Function.Injective j := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥β.ker => ((z : ↥⁅V, L⁆) : G)) hxy
    exact Nat.card_le_card_of_injective j hj
  have hC₁card : Nat.card C₁ = Nat.card βC.range * Nat.card βC.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange βC).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup βC.ker
  have hW₁card : Nat.card ↥(⁅V, L⁆ : Subgroup G) = Nat.card F ^ 2 * Nat.card β.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβ).toEquiv]
    congr 1
    rw [show Nat.card (Multiplicative (Fin 2 → F)) = Nat.card (Fin 2 → F) from rfl, P22x.card_vec2]
  have hoff : (centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).relIndex A * Nat.card C₁ ≤
      Nat.card ↥(⁅V, L⁆ : Subgroup G) := by
    rw [hidx, hC₁card, hW₁card, ← hBcard]
    calc Nat.card B * (Nat.card βC.range * Nat.card βC.ker)
        ≤ Nat.card B * (Nat.card (P22x.sl2Fix B) * Nat.card β.ker) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hrangeβ hkerβ)
      _ = Nat.card B * Nat.card (P22x.sl2Fix B) * Nat.card β.ker := by ring
      _ ≤ Nat.card F ^ 2 * Nat.card β.ker := Nat.mul_le_mul_right _ hbound
  set A₀ : Subgroup G := A ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) with hA₀def
  have hA₀N : A₀ ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ ha.2
  have hprod := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hA₀N
  have hinf : A₀ ⊓ ⁅V, L⁆ = A ⊓ ⁅V, L⁆ := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · intro x hx
      refine ⟨⟨hx.1, Subgroup.mem_centralizer_iff.2 ?_⟩, hx.2⟩
      intro w hw
      exact hWe.comm hw hx.2
  rw [hinf] at hprod
  have hAW : A ⊓ ⁅V, L⁆ ≤ C₁ := by
    intro x hx
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, hx.2⟩
    intro a ha
    exact hA.2.1.comm ha hx.1
  have hAcard : Nat.card A = (centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).relIndex A * Nat.card A₀ := by
    have h := Subgroup.index_mul_card ((centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).subgroupOf A)
    have h' : Nat.card ((centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).subgroupOf A) = Nat.card A₀ := by
      rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype, hA₀def,
        inf_comm]
    rw [h'] at h
    rw [Subgroup.relIndex]
    exact h.symm
  refine ⟨sup_le (inf_le_left.trans hA.1) hWT,
    (hA.2.1.mono inf_le_left).sup_of_commute hWe fun a ha w hw =>
      (Subgroup.mem_centralizer_iff.1 ha.2 w hw).symm, fun B hBT hB => (hA.2.2 B hBT hB).trans ?_⟩
  have hC₁pos : 0 < Nat.card C₁ := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hC₁pos
  calc Nat.card A * Nat.card C₁ =
        (centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).relIndex A * Nat.card A₀ * Nat.card C₁ := by
        rw [hAcard]
    _ = Nat.card A₀ * ((centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).relIndex A * Nat.card C₁) := by ring
    _ ≤ Nat.card A₀ * Nat.card ↥(⁅V, L⁆ : Subgroup G) := Nat.mul_le_mul_left _ hoff
    _ = Nat.card ↥(A₀ ⊔ ⁅V, L⁆) * Nat.card ↥(A ⊓ ⁅V, L⁆) := hprod.symm
    _ ≤ Nat.card ↥(A₀ ⊔ ⁅V, L⁆) * Nat.card C₁ := Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hAW)

end P22kA

end CFSG.LocalAnalysis.UniquenessCase.UC22
