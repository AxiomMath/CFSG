module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sh
import CFSG.Milestones.ASVolI.B6Baumann
import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.Quasithin (MinParabolic IsTwoReducedIn VZ thompsonJ baum kerIn)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace P22s

theorem Jj_zero (H : Subgroup G) : CFSG.ASVolI.ChB.Jj H 0 = thompsonJ H := by
  unfold CFSG.ASVolI.ChB.Jj
  rw [if_pos (Nat.zero_le _), CFSG.higherElemThompson_zero, CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ]

theorem baumOf_eq (H : Subgroup G) : CFSG.ASVolI.ChB.baumOf H = baum H := by
  unfold CFSG.ASVolI.ChB.baumOf CFSG.Quasithin.baum
  rw [Jj_zero]

omit [Finite G] in
theorem conjAct_coe {V : Subgroup G} (x : ↥(normalizer (V : Set G))) (v : ↥V) :
    ((CFSG.Quasithin.conjAct V x v : ↥V) : G) = (x : G) * v * (x : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem isSolvable_kerIn {H T M : Subgroup G} (h : MinParabolic H T M) : Group.IsSolvable ↥(kerIn M H) := by
  have hsol := h.subgroupOf.isSolvable_kerIn
  rw [CFSG.Quasithin.B6.kerIn_subgroupOf_top] at hsol
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe h.kerIn_le_H).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h.kerIn_le_H).surjective

theorem le_of_perfect_of_solvable {L Y P : Subgroup G} (hY : Group.IsSolvable ↥Y)
    (hYL : Y ≤ normalizer (L : Set G)) (hP : P ≤ L ⊔ Y) (hPp : ⁅P, P⁆ = P) : P ≤ L :=
  (CFSG.Quasithin.le_perfectCore_of_perfect hP hPp).trans
    (CFSG.Quasithin.perfectCore_le_of_sup_solvable le_sup_left
      (Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hYL)) rfl hY)

theorem conj_mem_of_perfect {L Y : Subgroup G} (hY : Group.IsSolvable ↥Y) (hYL : Y ≤ normalizer (L : Set G))
    (hLp : ⁅L, L⁆ = L) {x : G} (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L ⊔ Y) : ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
  have hP : ⁅L.map (MulAut.conj x).toMonoidHom, L.map (MulAut.conj x).toMonoidHom⁆ =
      L.map (MulAut.conj x).toMonoidHom := by
    rw [← Subgroup.map_commutator, hLp]
  have hle := le_of_perfect_of_solvable hY hYL (by
    rintro _ ⟨l, hl, rfl⟩
    exact hx l hl) hP
  intro l hl
  exact hle ⟨l, hl, rfl⟩

theorem le_normalizer_of_autOn {L L₀ V S : Subgroup G} (hB : Group.IsSolvable ↥(L₀ ⊓ centralizer (V : Set G)))
    (hL₀L : L₀ ≤ normalizer (L : Set G)) (hLL₀ : L ≤ L₀) (hLp : ⁅L, L⁆ = L) (hLV : L ≤ normalizer (V : Set G))
    (hSV : S ≤ normalizer (V : Set G)) (hSL₀ : S ≤ normalizer (L₀ : Set G))
    (h1 : ∀ s ∈ S, ∀ hs : s ∈ normalizer (V : Set G), CFSG.Quasithin.conjAct V ⟨s, hs⟩ ∈
      normalizer (CFSG.Quasithin.autOn L V : Set (MulAut ↥V))) :
    S ≤ normalizer (L : Set G) := by
  refine le_normalizer_of_conj fun s hs l hl =>
    conj_mem_of_perfect hB (inf_le_left.trans hL₀L) hLp (fun l hl => ?_) l hl
  have hsV := hSV hs
  have hlV := hLV hl
  have hmem : CFSG.Quasithin.conjAct V ⟨l, hlV⟩ ∈ CFSG.Quasithin.autOn L V := ⟨⟨l, hlV⟩, hl, rfl⟩
  obtain ⟨y, hyL, hy⟩ := (Subgroup.mem_normalizer_iff.1 (h1 s hs hsV) _).1 hmem
  have hy' : CFSG.Quasithin.conjAct V y =
      CFSG.Quasithin.conjAct V (⟨s, hsV⟩ * ⟨l, hlV⟩ * (⟨s, hsV⟩ : ↥(normalizer (V : Set G)))⁻¹) := by
    rw [hy, map_mul, map_mul, map_inv]
  have hcV : (y : G)⁻¹ * (s * l * s⁻¹) ∈ centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hy'
    simp only [conjAct_coe, Subgroup.coe_mul, Subgroup.coe_inv] at hv'
    calc v * ((y : G)⁻¹ * (s * l * s⁻¹)) = (y : G)⁻¹ * ((y : G) * v * (y : G)⁻¹) * (s * l * s⁻¹) := by group
      _ = (y : G)⁻¹ * (s * l * s⁻¹ * v * (s * l * s⁻¹)⁻¹) * (s * l * s⁻¹) := by rw [hv']
      _ = (y : G)⁻¹ * (s * l * s⁻¹) * v := by group
  have hyL₀ : (y : G) ∈ L₀ := hLL₀ hyL
  have hxL₀ : s * l * s⁻¹ ∈ L₀ := (Subgroup.mem_normalizer_iff.1 (hSL₀ hs) l).1 (hLL₀ hl)
  have hc : (y : G)⁻¹ * (s * l * s⁻¹) ∈ L₀ ⊓ centralizer (V : Set G) :=
    ⟨L₀.mul_mem (L₀.inv_mem hyL₀) hxL₀, hcV⟩
  have e : s * l * s⁻¹ = (y : G) * ((y : G)⁻¹ * (s * l * s⁻¹)) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hyL hc

@[expose] noncomputable def slEquiv (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(StatedSL 2 F) :=
  (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 F).symm)

theorem coe_slEquiv_symm (F : Type) [Field F] (x : ↥(StatedSL 2 F)) :
    (((slEquiv F).symm x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨A, rfl⟩ := (slEquiv F).surjective x
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem eq_one_of_central {F : Type} [Field F] [Fintype F] {e : ℕ} (hF : Fintype.card F = 2 ^ e) (he : 1 ≤ e)
    {A : ↥(StatedSL 2 F)} (hA : ∀ B : ↥(StatedSL 2 F), A * B = B * A) : A = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchp : CharP F 2 := charP_of_card_eq_prime_pow hF
  set A' : Matrix.SpecialLinearGroup (Fin 2) F := (slEquiv F).symm A with hA'
  have hcen : A' ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply (slEquiv F).injective
    rw [map_mul, map_mul, hA', MulEquiv.apply_symm_apply]
    exact (hA _).symm
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hsq : (r - 1) ^ 2 = 0 := by
    have : (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
    rw [this, hr2]
    linear_combination (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 hsq)
  have hA'1 : A' = 1 := by
    ext i j
    rw [← hrA, hr1]
    simp
  calc A = slEquiv F A' := by rw [hA', MulEquiv.apply_symm_apply]
    _ = 1 := by rw [hA'1, map_one]

section Natural

variable {L V : Subgroup G} {F : Type} [Field F] [Fintype F]

theorem alpha_conj_eq (α : ↥L →* ↥(StatedSL 2 F)) (β : ↥⁅V, L⁆ →* Multiplicative (Fin 2 → F))
    (hβ : Function.Surjective β)
    (hβα : ∀ (l : ↥L) (u v : ↥⁅V, L⁆), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β v) = (((α l : ↥(StatedSL 2 F)) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hLV : L ≤ normalizer (V : Set G)) {g : G} (hgL : g ∈ normalizer (L : Set G))
    (hgV : g ∈ normalizer (V : Set G)) (hg : ∀ u v : ↥⁅V, L⁆, (v : G) = g * u * g⁻¹ → β v = β u)
    (l : ↥L) : α ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgL l).1 l.2⟩ = α l := by
  have hgW : g ∈ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := CFSG.Quasithin.SBd5.mem_normalizer_commutator_of hgV hgL
  have hlW : (l : G) ∈ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    CFSG.Quasithin.SBd5.mem_normalizer_commutator_of (hLV l.2) (Subgroup.le_normalizer l.2)
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro x
  obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd x)
  have hx : Multiplicative.toAdd (β u) = x := by rw [hu]; rfl
  rw [← hx]
  have hu' : g⁻¹ * u * g ∈ ⁅V, L⁆ := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgW) (u : G)).1 u.2
    simpa using this
  have hβu : β u = β ⟨g⁻¹ * u * g, hu'⟩ := hg ⟨g⁻¹ * u * g, hu'⟩ u (by simp only; group)
  have hu'' : (l : G) * (g⁻¹ * u * g) * (l : G)⁻¹ ∈ ⁅V, L⁆ := (Subgroup.mem_normalizer_iff.1 hlW _).1 hu'
  have hw : g * l * g⁻¹ * u * (g * l * g⁻¹)⁻¹ ∈ ⁅V, L⁆ := by
    have := (Subgroup.mem_normalizer_iff.1 hgW _).1 hu''
    have e : g * l * g⁻¹ * u * (g * l * g⁻¹)⁻¹ = g * ((l : G) * (g⁻¹ * u * g) * (l : G)⁻¹) * g⁻¹ := by group
    rw [e]
    exact this
  have h1 := hβα ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgL l).1 l.2⟩ u ⟨_, hw⟩ rfl
  have h2 : β ⟨_, hw⟩ = β ⟨_, hu''⟩ := hg ⟨_, hu''⟩ ⟨_, hw⟩ (by simp only; group)
  have h3 := hβα l ⟨g⁻¹ * u * g, hu'⟩ ⟨_, hu''⟩ rfl
  rw [← h1, h2, h3, ← hβu]

theorem mem_centralizer_of_trivial (α : ↥L →* ↥(StatedSL 2 F))
    (hαk : α.ker = (L ⊓ centralizer (V : Set G)).subgroupOf L)
    (β : ↥⁅V, L⁆ →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβk : β.ker = (⁅V, L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (hβα : ∀ (l : ↥L) (u v : ↥⁅V, L⁆), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β v) = (((α l : ↥(StatedSL 2 F)) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hLV : L ≤ normalizer (V : Set G)) (hLp : ⁅L, L⁆ = L)
    {g : G} (hgL : g ∈ normalizer (L : Set G)) (hgV : g ∈ normalizer (V : Set G))
    (hg : ∀ u v : ↥⁅V, L⁆, (v : G) = g * u * g⁻¹ → β v = β u) : g ∈ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hgW : g ∈ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := CFSG.Quasithin.SBd5.mem_normalizer_commutator_of hgV hgL
  have key : ∀ w ∈ ⁅V, L⁆, ∀ l ∈ L, g * ⁅w, l⁆ * g⁻¹ = ⁅w, l⁆ := by
    intro w hw l hl
    have hgw : g * w * g⁻¹ ∈ ⁅V, L⁆ := (Subgroup.mem_normalizer_iff.1 hgW w).1 hw
    have hw₀ : w⁻¹ * (g * w * g⁻¹) ∈ ⁅V, L⁆ ⊓ centralizer (L : Set G) := by
      have h1 : β ⟨g * w * g⁻¹, hgw⟩ = β ⟨w, hw⟩ := hg ⟨w, hw⟩ ⟨_, hgw⟩ rfl
      have h2 : (⟨w, hw⟩ : ↥⁅V, L⁆)⁻¹ * ⟨g * w * g⁻¹, hgw⟩ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      rw [hβk, Subgroup.mem_subgroupOf] at h2
      exact h2
    have hglg : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hgL l).1 hl
    have hc : g * l * g⁻¹ * l⁻¹ ∈ centralizer (V : Set G) := by
      have h1 := alpha_conj_eq α β hβ hβα hLV hgL hgV hg ⟨l, hl⟩
      have h2 : (⟨g * l * g⁻¹, hglg⟩ : ↥L) * (⟨l, hl⟩ : ↥L)⁻¹ ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
      rw [hαk, Subgroup.mem_subgroupOf] at h2
      exact h2.2
    set w₀ : G := w⁻¹ * (g * w * g⁻¹) with hw₀def
    set c : G := g * l * g⁻¹ * l⁻¹ with hcdef
    have hgw' : g * w * g⁻¹ = w * w₀ := by rw [hw₀def]; group
    have hgl' : g * l * g⁻¹ = c * l := by rw [hcdef]; group
    have hwV : w ∈ V := hWV hw
    have hw₀V : w₀ ∈ V := hWV hw₀.1
    have hwl : w * l * w⁻¹ * l⁻¹ ∈ V := by
      have : l * w⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hl) _).1 (V.inv_mem hwV)
      have e : w * l * w⁻¹ * l⁻¹ = w * (l * w⁻¹ * l⁻¹) := by group
      rw [e]
      exact V.mul_mem hwV this
    have e1 : w₀ * (c * l) = c * l * w₀ := by
      have hc1 : w₀ * c = c * w₀ := (Subgroup.mem_centralizer_iff.1 hc w₀ hw₀V)
      have hl1 : l * w₀ = w₀ * l := Subgroup.mem_centralizer_iff.1 hw₀.2 l hl
      calc w₀ * (c * l) = (w₀ * c) * l := by group
        _ = c * (w₀ * l) := by rw [hc1]; group
        _ = c * l * w₀ := by rw [← hl1]; group
    have e2 : w * c = c * w := Subgroup.mem_centralizer_iff.1 hc w hwV
    have e3 : (w * l * w⁻¹ * l⁻¹) * c = c * (w * l * w⁻¹ * l⁻¹) := Subgroup.mem_centralizer_iff.1 hc _ hwl
    rw [commutatorElement_def]
    calc g * (w * l * w⁻¹ * l⁻¹) * g⁻¹
        = (g * w * g⁻¹) * (g * l * g⁻¹) * (g * w * g⁻¹)⁻¹ * (g * l * g⁻¹)⁻¹ := by group
      _ = (w * w₀) * (c * l) * (w * w₀)⁻¹ * (c * l)⁻¹ := by rw [hgw', hgl']
      _ = w * (w₀ * (c * l)) * w₀⁻¹ * w⁻¹ * (c * l)⁻¹ := by group
      _ = w * (c * l * w₀) * w₀⁻¹ * w⁻¹ * (c * l)⁻¹ := by rw [e1]
      _ = (w * c) * l * w⁻¹ * l⁻¹ * c⁻¹ := by group
      _ = (c * w) * l * w⁻¹ * l⁻¹ * c⁻¹ := by rw [e2]
      _ = c * (w * l * w⁻¹ * l⁻¹) * c⁻¹ := by group
      _ = (w * l * w⁻¹ * l⁻¹) * c * c⁻¹ := by rw [← e3]
      _ = w * l * w⁻¹ * l⁻¹ := by group
  have hWL : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ := CFSG.Quasithin.SBd5.commutator_commutator_eq_self hLp hLV hV
  have hle : ⁅⁅V, L⁆, L⁆ ≤ centralizer ({g} : Set G) := by
    rw [Subgroup.commutator_le]
    intro w hw l hl
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    calc g * ⁅w, l⁆ = g * ⁅w, l⁆ * g⁻¹ * g := by group
      _ = ⁅w, l⁆ * g := by rw [key w hw l hl]
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [← hWL] at hh
  exact (Subgroup.mem_centralizer_iff.1 (hle hh) g rfl).symm

theorem le_commutator_of_inner {S : Subgroup G} {e : ℕ} (hF : Fintype.card F = 2 ^ e) (he : 1 ≤ e)
    (α : ↥L →* ↥(StatedSL 2 F)) (hα : Function.Surjective α)
    (hαk : α.ker = (L ⊓ centralizer (V : Set G)).subgroupOf L)
    (β : ↥⁅V, L⁆ →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβk : β.ker = (⁅V, L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (hβα : ∀ (l : ↥L) (u v : ↥⁅V, L⁆), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β v) = (((α l : ↥(StatedSL 2 F)) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hLV : L ≤ normalizer (V : Set G)) (hLp : ⁅L, L⁆ = L)
    (hLq : CFSG.Open.IsQuasisimple (Bar2 L)) (hO : pCoreOf 2 L ≤ centralizer (V : Set G))
    (hSL : S ≤ normalizer (L : Set G)) (hSV : S ≤ normalizer (V : Set G))
    (hinn : ∀ b ∈ S, ∃ l ∈ L, ∀ u v : ↥⁅V, L⁆, (v : G) = (l⁻¹ * b) * u * (l⁻¹ * b)⁻¹ → β v = β u)
    (hne : ¬ S ≤ centralizer ((⁅V, L⁆ : Subgroup G) : Set G)) : L ≤ ⁅S, L⁆ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hNL : ⁅S, L⁆ ≤ L := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hSL
  have hLN : L ≤ normalizer ((⁅S, L⁆ : Subgroup G) : Set G) := Subgroup.normalizer_commutator_ge_right S L
  haveI hNn : ((⁅S, L⁆ : Subgroup G).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2 hLN
  have hcentral : ∀ x : ↥L, (∀ l : ↥L, α x * α l = α l * α x) → (x : G) ∈ centralizer (V : Set G) := by
    intro x hx
    have h1 : α x = 1 := eq_one_of_central hF he fun B => by
      obtain ⟨l, rfl⟩ := hα B
      exact hx l
    have h2 : x ∈ α.ker := h1
    rw [hαk, Subgroup.mem_subgroupOf] at h2
    exact h2.2
  have hpk : CFSG.pCore 2 ↥L ≤ α.ker := fun x hx => by
    rw [hαk, Subgroup.mem_subgroupOf]
    exact ⟨x.2, hO ⟨x, hx, rfl⟩⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hLq)
      (N := ((⁅S, L⁆ : Subgroup G).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
      (hNn.map _ (QuotientGroup.mk'_surjective _)) with htop | hcen
  ·
    refine le_of_commutator_eq_self (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLN) (fun l hl => ?_) hLp
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩ ∈
        ((⁅S, L⁆ : Subgroup G).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnl⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
    have e : l = (n : G) * ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup hn ⟨_, hnl, rfl⟩
  · exfalso
    have hNC : ∀ x ∈ ⁅S, L⁆, x ∈ centralizer (V : Set G) := by
      intro x hx
      refine hcentral ⟨x, hNL hx⟩ fun l => ?_
      have hmn : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hNL hx⟩ ∈ Subgroup.center (Bar2 L) :=
        hcen ⟨⟨x, hNL hx⟩, hx, rfl⟩
      have h1 := (Subgroup.mem_center_iff.1 hmn) (QuotientGroup.mk' _ l)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      have h2 := hpk h1
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h2
      exact h2.symm
    apply hne
    intro b hb
    obtain ⟨lb, hlb, hlbb⟩ := hinn b hb
    have hgL : lb⁻¹ * b ∈ normalizer (L : Set G) :=
      mul_mem (inv_mem (Subgroup.le_normalizer hlb)) (hSL hb)
    have hgV : lb⁻¹ * b ∈ normalizer (V : Set G) := mul_mem (inv_mem (hLV hlb)) (hSV hb)
    have hlbC : lb ∈ centralizer (V : Set G) := by
      refine hcentral ⟨lb, hlb⟩ fun l => ?_
      have hbl : b * l * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hSL hb) l).1 l.2
      have h1 : α ⟨b * l * b⁻¹, hbl⟩ = α l := by
        have hk : (⟨b * l * b⁻¹, hbl⟩ : ↥L) * l⁻¹ ∈ α.ker := by
          rw [hαk, Subgroup.mem_subgroupOf]
          exact ⟨L.mul_mem hbl (L.inv_mem l.2),
            hNC _ (Subgroup.commutator_mem_commutator hb l.2)⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
        exact hk
      have h2 := alpha_conj_eq α β hβ hβα hLV hgL hgV hlbb l
      have h3 : (⟨b * l * b⁻¹, hbl⟩ : ↥L) =
          ⟨lb, hlb⟩ * ⟨(lb⁻¹ * b) * l * (lb⁻¹ * b)⁻¹, (Subgroup.mem_normalizer_iff.1 hgL l).1 l.2⟩ *
            (⟨lb, hlb⟩ : ↥L)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h3, map_mul, map_mul, h2, map_inv] at h1
      calc α ⟨lb, hlb⟩ * α l = (α ⟨lb, hlb⟩ * α l * (α ⟨lb, hlb⟩)⁻¹) * α ⟨lb, hlb⟩ := by group
        _ = α l * α ⟨lb, hlb⟩ := by rw [h1]
    refine mem_centralizer_of_trivial α hαk β hβ hβk hβα hV hLV hLp (hSL hb) (hSV hb) fun u v huv => ?_
    have hgu : (lb⁻¹ * b) * u * (lb⁻¹ * b)⁻¹ ∈ ⁅V, L⁆ := by
      have hgW := CFSG.Quasithin.SBd5.mem_normalizer_commutator_of hgV hgL
      exact (Subgroup.mem_normalizer_iff.1 hgW u).1 u.2
    have hv : (v : G) = (lb⁻¹ * b) * u * (lb⁻¹ * b)⁻¹ := by
      have hcomm := Subgroup.mem_centralizer_iff.1 hlbC _ (hWV hgu)
      rw [huv]
      calc b * u * b⁻¹ = lb * ((lb⁻¹ * b) * u * (lb⁻¹ * b)⁻¹) * lb⁻¹ := by group
        _ = (lb⁻¹ * b) * u * (lb⁻¹ * b)⁻¹ * lb * lb⁻¹ := by rw [hcomm]
        _ = (lb⁻¹ * b) * u * (lb⁻¹ * b)⁻¹ := by group
    exact hlbb u v hv

end Natural

end P22s

open P22s

theorem uc22p22sl_b610 {D : Data G} {Ch : Choice2011 G} (h204 : S20_4 D) (hH : H1930 D) (c : Ctx22c D Ch)
    (hS7 : normalizer (proofS D : Set G) ≤ D.M) {L : Subgroup G} {e : ℕ}
    (hLsub : CFSG.Open.IsSubnormal L (c.L0 ⊔ D.T)) (hLL0 : L ≤ c.L0) (hL0L : c.L0 ≤ normalizer (L : Set G))
    (hLp : ⁅L, L⁆ = L) (he : 2 ≤ e) (hnat : NatSL2 L (VZ D.T (c.L0 ⊔ D.T)) e) :
    proofS D ≤ normalizer (L : Set G) ∧
      CFSG.QuasithinUnique.IsSylowTwoOf (proofS D) (⨆ l ∈ L, (proofS D).map (MulAut.conj l).toMonoidHom) ∧
      proofE D = (⁅VZ D.T (c.L0 ⊔ D.T), L⁆ ⊓ centralizer (thompsonJ D.T : Set G)) ⊔
        (proofE D ⊓ centralizer (L : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := c.L0 ⊔ D.T with hHdef
  set V₀ : Subgroup G := VZ D.T H with hV₀
  obtain ⟨hU, hJV, -, hred⟩ := uc22p22se_ffModule c hS7
  have hMP := uc22p22se_minParabolic h204 hH c.toCtx21
  have hFq : quasithinGenFitting H = pCoreOf 2 H :=
    (CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff H 2).2 (uc22p22se_charTwo c.toCtx21)
  have hHN : H ≤ normalizer (V₀ : Set G) := hred.2.1
  have hLN : L ≤ normalizer (V₀ : Set G) := hLL0.trans (le_sup_left.trans hHN)
  have hJ' : ⁅V₀, CFSG.ASVolI.ChB.Jj D.T 0⁆ ≠ ⊥ := by
    rw [Jj_zero]
    intro hbot
    apply hJV
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hbot
  obtain ⟨h1, h2, h3⟩ := CFSG.ASVolI.as_B_6_10 G H D.T (H ⊓ D.M) V₀ L e hMP hFq hred hLsub
    (isNaturalL2Prime_of_natSL2 (by omega) hLN hnat) hJ'
  rw [baumOf_eq, ← uc22p22se_proofS_eq] at h1 h2
  rw [Jj_zero] at h3
  refine ⟨?_, h2, ?_⟩
  · have hle : c.L0 ⊓ centralizer (V₀ : Set G) ≤ kerIn (H ⊓ D.M) H :=
      (inf_le_inf_right _ le_sup_left).trans
        (hMP.inf_centralizer_le_kerIn hred (uc22p22se_not_le_centralizer_V0 c))
    haveI := isSolvable_kerIn hMP
    have hB : Group.IsSolvable ↥(c.L0 ⊓ centralizer (V₀ : Set G)) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    exact le_normalizer_of_autOn hB hL0L hLL0 hLp hLN
      (fun s hs => hHN (Subgroup.mem_sup_right hs.1)) (fun s hs => c.hL0.1.1 hs.1) h1
  · rw [uc22p22se_proofE_eq]
    exact h3 (CFSG.Quasithin.C126.Nat.twoResidual_eq_of_perfect hLp)

theorem uc22p22sl_le_M_of_commutator_eq_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx22c D Ch)
    (hS7 : normalizer (proofS D : Set G) ≤ D.M) {L : Subgroup G}
    (hLN : L ≤ normalizer (VZ D.T (c.L0 ⊔ D.T) : Set G))
    (hE : proofE D = (⁅VZ D.T (c.L0 ⊔ D.T), L⁆ ⊓ centralizer (thompsonJ D.T : Set G)) ⊔
      (proofE D ⊓ centralizer (L : Set G)))
    (hJW : ⁅thompsonJ D.T, ⁅VZ D.T (c.L0 ⊔ D.T), L⁆⁆ = ⊥) : L ≤ D.M := by
  have hW : ⁅VZ D.T (c.L0 ⊔ D.T), L⁆ ≤ centralizer (thompsonJ D.T : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hJW
  have hLW : L ≤ normalizer ((⁅VZ D.T (c.L0 ⊔ D.T), L⁆ : Subgroup G) : Set G) := fun l hl =>
    CFSG.Quasithin.SBd5.mem_normalizer_commutator_of (hLN hl) (Subgroup.le_normalizer hl)
  have hLC : L ≤ normalizer ((proofE D ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh =>
      (Subgroup.mem_centralizer_iff.1 hh.2 l hl).symm)
  have hLE : L ≤ normalizer (proofE D : Set G) := by
    rw [hE, inf_eq_left.2 hW]
    exact CFSG.Quasithin.B2F.le_normalizer_sup hLW hLC
  exact hLE.trans (uc22p22se_normalizer_proofE_le D hS7 c.hCle)

end CFSG.LocalAnalysis.UniquenessCase.UC22
