module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RThree
import CFSG.Quasithin.Vol2.Ch10SecQ6SL2b

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open Matrix
open scoped commutatorElement

open HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem card_LB_eq_card_inf_mul (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) :
    Nat.card (LB M Q B) = Nat.card Z * Nat.card ↥(LB M Q B ⊓ X) := by
  have h := Subgroup.relIndex_mul_card (H := LB M Q B ⊓ X) (K := LB M Q B)
  rw [inf_eq_left.mpr (inf_le_left : LB M Q B ⊓ X ≤ LB M Q B),
    HS9.relIndex_LB_inf_X hc hsplit h4] at h
  exact h.symm

private theorem card_inf_ge (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) :
    Nat.card Q * Nat.card Z ^ (n - 2) ≤ Nat.card ↥(LB M Q B ⊓ X) := by
  have hs5 := hs.toSec5
  have hn2' : 2 < n := hs5.n_gt
  have hn2 : 2 ≤ n := by omega
  have hLB := hc.card_LB_ge hs5.width (by omega : 1 ≤ n)
  have hcard := card_LB_eq_card_inf_mul hc hsplit h4
  have hpow : Nat.card Z ^ (n - 1) = Nat.card Z * Nat.card Z ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, mul_comm]
  have h' : (Nat.card Q * Nat.card Z ^ (n - 2)) * Nat.card Z ≤
      Nat.card ↥(LB M Q B ⊓ X) * Nat.card Z := by
    calc (Nat.card Q * Nat.card Z ^ (n - 2)) * Nat.card Z
        = Nat.card Q * Nat.card Z ^ (n - 1) := by rw [hpow]; ring
      _ ≤ Nat.card (LB M Q B) := hLB
      _ = Nat.card Z * Nat.card ↥(LB M Q B ⊓ X) := hcard
      _ = Nat.card ↥(LB M Q B ⊓ X) * Nat.card Z := by ring
  exact Nat.le_of_mul_le_mul_right h' (Nat.card_pos (α := ↥Z))

private theorem exists_mem_inf_not_mem_Q (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) :
    ∃ e ∈ LB M Q B ⊓ X, e ∉ Q := by
  by_contra hno
  push Not at hno
  have hle : LB M Q B ⊓ X ≤ Q := fun x hx => hno x hx
  have hcardle := Subgroup.card_le_of_le hle
  have hge := card_inf_ge hc hs hsplit h4
  have hn4 := HS6.four_le_of_omegaPlus_two h34 hc hs.toSec5 hs.plus4
  have hq4 := hc.hyp.q4
  have hpow : 1 < Nat.card Z ^ (n - 2) := by
    calc 1 < 4 ^ 2 := by norm_num
      _ ≤ Nat.card Z ^ 2 := Nat.pow_le_pow_left hq4 2
      _ ≤ Nat.card Z ^ (n - 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : Nat.card Q < Nat.card Q * Nat.card Z ^ (n - 2) :=
    (Nat.lt_mul_iff_one_lt_right (Nat.card_pos (α := ↥Q))).mpr hpow
  omega

private noncomputable def conjAction (F Y : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) : ↥F →* MulAut ↥Y :=
  (Subgroup.normalizerMonoidHom Y).comp (Subgroup.inclusion hFN)

private theorem conjAction_apply (F Y : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) (f : ↥F) (y : ↥Y) :
    ((conjAction F Y hFN f y : ↥Y) : G) = (f : G) * (y : G) * (f : G)⁻¹ := by
  rw [conjAction, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion]

private theorem conjAction_quotient_invariant (M F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hFM : F ≤ M) (hQM : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q) :
    ∀ f : ↥F, (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y := by
  intro f
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    change (z : G) ∈ Q at hz
    have hact : (((conjAction F Y hFN f) z : ↥Y) : G) = (f : G) * (z : G) * (f : G)⁻¹ :=
      conjAction_apply F Y hFN f z
    rw [← hzy]
    change (((conjAction F Y hFN f) z : ↥Y) : G) ∈ Q
    rw [hact]
    exact hQM (f : G) (hFM f.2) (z : G) hz
  · intro hy
    rw [Subgroup.mem_map]
    refine ⟨conjAction F Y hFN f⁻¹ y, ?_, ?_⟩
    · change (((conjAction F Y hFN f⁻¹ y : ↥Y) : G)) ∈ Q
      rw [conjAction_apply]
      have hfinv : ((f⁻¹ : ↥F) : G) = (f : G)⁻¹ := rfl
      rw [hfinv]
      exact hQM (f : G)⁻¹ (M.inv_mem (hFM f.2)) (y : G) (Subgroup.mem_subgroupOf.mp hy)
    · have h1 : conjAction F Y hFN f * conjAction F Y hFN f⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      change conjAction F Y hFN f (conjAction F Y hFN f⁻¹ y) = y
      rw [← MulAut.mul_apply, h1, MulAut.one_apply]

private noncomputable def conjQuotAction (F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y) :
    ↥F →* MulAut (↥Y ⧸ Q.subgroupOf Y) :=
  CFSG.OrderReductions.InvariantQuotient.quotientHomomorphism (conjAction F Y hFN)
    (Q.subgroupOf Y) hQinv

private theorem conjQuotAction_apply (F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y)
    (f : ↥F) (y : ↥Y) :
    conjQuotAction F Y Q hFN hQinv f (QuotientGroup.mk' (Q.subgroupOf Y) y) =
      QuotientGroup.mk' (Q.subgroupOf Y) (conjAction F Y hFN f y) := by
  change CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism
    (conjAction F Y hFN f) (Q.subgroupOf Y) (hQinv f)
    (QuotientGroup.mk' (Q.subgroupOf Y) y) = _
  rw [CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply]

private theorem conjQuotAction_ker_iff (F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y)
    (f : ↥F) :
    f ∈ (conjQuotAction F Y Q hFN hQinv).ker ↔
      ∀ y : ↥Y, ⁅(f : G), (y : G)⁆ ∈ Q := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hf y
    have h1 : conjQuotAction F Y Q hFN hQinv f
        (QuotientGroup.mk' (Q.subgroupOf Y) y) =
        QuotientGroup.mk' (Q.subgroupOf Y) y := by
      rw [hf, MulAut.one_apply]
    rw [conjQuotAction_apply] at h1
    change (QuotientGroup.mk (((conjAction F Y hFN) f) y) : ↥Y ⧸ Q.subgroupOf Y) =
      QuotientGroup.mk y at h1
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at h1
    change ((↑(((conjAction F Y hFN) f) y) : G) / ↑y : G) ∈ Q at h1
    have h2 : ((↑(((conjAction F Y hFN) f) y) : G) / ↑y : G) = ⁅(f : G), (y : G)⁆ := by
      rw [conjAction_apply, commutatorElement_def, div_eq_mul_inv]
    rwa [h2] at h1
  · intro hf
    apply MulEquiv.ext
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf Y) z
    rw [conjQuotAction_apply, MulAut.one_apply]
    change (QuotientGroup.mk (((conjAction F Y hFN) f) y) : ↥Y ⧸ Q.subgroupOf Y) =
      QuotientGroup.mk y
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    change ((↑(((conjAction F Y hFN) f) y) : G) / ↑y : G) ∈ Q
    have h2 : ((↑(((conjAction F Y hFN) f) y) : G) / ↑y : G) = ⁅(f : G), (y : G)⁆ := by
      rw [conjAction_apply, commutatorElement_def, div_eq_mul_inv]
    rw [h2]
    exact hf y

private theorem conjSubgroup_le_M (hc : Ctx M Q Z B) {X : Subgroup G} {g : G} (hg : g ∈ M) :
    conjSubgroup g (LB M Q B ⊓ X) ≤ M := by
  intro f hf
  have h0 : g⁻¹ * f * g ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hf
  have h1 := M.mul_mem (M.mul_mem hg (hc.LB_le_M h0.1)) (M.inv_mem hg)
  rwa [show g * (g⁻¹ * f * g) * g⁻¹ = f by group] at h1

private theorem conjSubgroup_le_normalizer (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h1 : OneConcl hc X Y) {g e₀ : G} (hg : g ∈ M)
    (he₀ : e₀ ∈ LB M Q B ⊓ X) (he₀Q : e₀ ∉ Q)
    (hcommQ : ∀ f ∈ conjSubgroup g (LB M Q B ⊓ X), ∀ e ∈ LB M Q B ⊓ X, ⁅f, e⁆ ∈ Q) :
    conjSubgroup g (LB M Q B ⊓ X) ≤ Subgroup.normalizer (Y : Set G) := by
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, -, -, -, -, -, -⟩, -, -⟩ := hsplit
  intro f hf
  have hfM : f ∈ M := conjSubgroup_le_M hc hg hf
  have hQE : Q ≤ LB M Q B ⊓ X := le_inf le_sup_left hQX
  have hfe : f * e₀ * f⁻¹ ∈ LB M Q B ⊓ X := by
    have hq : ⁅f, e₀⁆ ∈ Q := hcommQ f hf e₀ he₀
    have e : f * e₀ * f⁻¹ = ⁅f, e₀⁆ * e₀ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (LB M Q B ⊓ X).mul_mem (hQE hq) he₀
  exact conjSubgroup_eq_self_iff.mp
    (HS9.conj_Y_eq_of_conj_mem hc hsplit0 h1 he₀ he₀Q hfM hfe)

private theorem commutator_mem_Q_of_mem_conj (hc : Ctx M Q Z B) {X : Subgroup G} {g f f' : G}
    (hg : g ∈ M) (hf : f ∈ conjSubgroup g (LB M Q B ⊓ X))
    (hf' : f' ∈ conjSubgroup g (LB M Q B ⊓ X)) : ⁅f, f'⁆ ∈ Q := by
  have he : g⁻¹ * f * g ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hf
  have he' : g⁻¹ * f' * g ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hf'
  have hQ : ⁅g⁻¹ * f * g, g⁻¹ * f' * g⁆ ∈ Q :=
    Subgroup.commutator_le.mp hc.commutator_LB_le_Q _ he.1 _ he'.1
  have e : ⁅f, f'⁆ = g * ⁅g⁻¹ * f * g, g⁻¹ * f' * g⁆ * g⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) _).mp hQ

private theorem sq_mem_Q_of_mem_conj (hc : Ctx M Q Z B) {X : Subgroup G} {g f : G}
    (hg : g ∈ M) (hf : f ∈ conjSubgroup g (LB M Q B ⊓ X)) : f ^ 2 ∈ Q := by
  have he : g⁻¹ * f * g ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hf
  have hQ : (g⁻¹ * f * g) ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB he.1
  have e : f ^ 2 = g * (g⁻¹ * f * g) ^ 2 * g⁻¹ := by
    rw [pow_two, pow_two]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) _).mp hQ

private theorem exists_mem_ker_not_mem {F : Subgroup G} {R : Type} [Group R] {n : ℕ}
    {X : Subgroup G} (ψ : ↥F →* MulAut R)
    (hcardR : Nat.card ψ.range ≤ Nat.card Z)
    (hcardF : Nat.card ↥F = Nat.card ψ.range * Nat.card ψ.ker)
    (hcardE : Nat.card ↥F = Nat.card ↥(LB M Q B ⊓ X))
    (hge : Nat.card Q * Nat.card Z ^ (n - 2) ≤ Nat.card ↥(LB M Q B ⊓ X))
    (hn4 : 4 ≤ n) (hq4 : 4 ≤ Nat.card Z) (hQF : Q ≤ F) :
    ∃ f ∈ ψ.ker, f ∉ Q.subgroupOf F := by
  have hcardQ : Nat.card ↥(Q.subgroupOf F) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQF).toEquiv
  have h1 : Nat.card Q * Nat.card Z ^ (n - 2) ≤
      Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← hcardF, hcardE]
    exact hge
  have hpow : Nat.card Z ^ (n - 2) = Nat.card Z * Nat.card Z ^ (n - 3) := by
    rw [show n - 2 = (n - 3) + 1 by omega, pow_succ, mul_comm]
  have hstep1 : Nat.card Q * (Nat.card Z * Nat.card Z ^ (n - 3)) ≤
      Nat.card Z * Nat.card ψ.ker := by
    calc Nat.card Q * (Nat.card Z * Nat.card Z ^ (n - 3))
        = Nat.card Q * Nat.card Z ^ (n - 2) := by rw [hpow]
      _ ≤ Nat.card ψ.range * Nat.card ψ.ker := h1
      _ ≤ Nat.card Z * Nat.card ψ.ker := Nat.mul_le_mul_right _ hcardR
  have hstep2 : (Nat.card Q * Nat.card Z ^ (n - 3)) * Nat.card Z ≤
      Nat.card ψ.ker * Nat.card Z := by
    calc (Nat.card Q * Nat.card Z ^ (n - 3)) * Nat.card Z
        = Nat.card Q * (Nat.card Z * Nat.card Z ^ (n - 3)) := by ring
      _ ≤ Nat.card Z * Nat.card ψ.ker := hstep1
      _ = Nat.card ψ.ker * Nat.card Z := by ring
  have hstep3 : Nat.card Q * Nat.card Z ^ (n - 3) ≤ Nat.card ψ.ker :=
    Nat.le_of_mul_le_mul_right hstep2 (Nat.card_pos (α := ↥Z))
  have hpow3 : 1 < Nat.card Z ^ (n - 3) := by
    have hn3 : n - 3 ≠ 0 := by
      have := hn4
      omega
    have hq1 : 1 < Nat.card Z := by
      have := hq4
      omega
    exact Nat.one_lt_pow hn3 hq1
  have hlt : Nat.card Q < Nat.card Q * Nat.card Z ^ (n - 3) :=
    (Nat.lt_mul_iff_one_lt_right (Nat.card_pos (α := ↥Q))).mpr hpow3
  have hltker : Nat.card Q < Nat.card ψ.ker := by omega
  by_contra hno
  push Not at hno
  have hle : ψ.ker ≤ Q.subgroupOf F := fun f hf => hno f hf
  have hcardle := Subgroup.card_le_of_le hle
  rw [hcardQ] at hcardle
  omega

private theorem conjQuotAction_q_mem_ker (M F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y)
    (hQM : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q) (hYM : Y ≤ M)
    (q : ↥F) (hq : (q : G) ∈ Q) :
    q ∈ (conjQuotAction F Y Q hFN hQinv).ker := by
  rw [MonoidHom.mem_ker]
  refine (conjQuotAction_ker_iff F Y Q hFN hQinv q).mpr fun y => ?_
  have h1 : (y : G) * (q : G)⁻¹ * (y : G)⁻¹ ∈ Q :=
    hQM (y : G) (hYM y.2) (q : G)⁻¹ (Q.inv_mem hq)
  have h2 : ⁅(q : G), (y : G)⁆ = (q : G) * ((y : G) * (q : G)⁻¹ * (y : G)⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact Q.mul_mem hq h1

private theorem conjQuotAction_range_comm (F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y)
    (hQker : ∀ q : ↥F, q ∈ Q.subgroupOf F →
      q ∈ (conjQuotAction F Y Q hFN hQinv).ker)
    (hcomm : ∀ f ∈ F, ∀ f' ∈ F, ⁅(f : G), (f' : G)⁆ ∈ Q) :
    ∀ a ∈ (conjQuotAction F Y Q hFN hQinv).range,
      ∀ b ∈ (conjQuotAction F Y Q hFN hQinv).range, a * b = b * a := by
  rintro _ ⟨f, rfl⟩ _ ⟨f', rfl⟩
  have hq := hcomm f f.2 f' f'.2
  let qF : ↥F := f * f' * f⁻¹ * f'⁻¹
  have hqF : qF ∈ Q.subgroupOf F := by
    change ((f : G) * (f' : G) * (f : G)⁻¹ * (f' : G)⁻¹) ∈ Q
    rwa [show (f : G) * (f' : G) * (f : G)⁻¹ * (f' : G)⁻¹ =
      ⁅(f : G), (f' : G)⁆ by rw [commutatorElement_def]]
  have h1 : f * f' = qF * (f' * f) := by
    ext
    change (f : G) * (f' : G) =
      ((f : G) * (f' : G) * (f : G)⁻¹ * (f' : G)⁻¹) * ((f' : G) * (f : G))
    group
  calc conjQuotAction F Y Q hFN hQinv f * conjQuotAction F Y Q hFN hQinv f'
      = conjQuotAction F Y Q hFN hQinv (f * f') := (map_mul _ f f').symm
    _ = conjQuotAction F Y Q hFN hQinv (qF * (f' * f)) := by rw [h1]
    _ = conjQuotAction F Y Q hFN hQinv qF *
        conjQuotAction F Y Q hFN hQinv (f' * f) := map_mul _ qF _
    _ = 1 * conjQuotAction F Y Q hFN hQinv (f' * f) := by
      rw [MonoidHom.mem_ker.mp (hQker qF hqF)]
    _ = conjQuotAction F Y Q hFN hQinv (f' * f) := one_mul _
    _ = conjQuotAction F Y Q hFN hQinv f' * conjQuotAction F Y Q hFN hQinv f :=
      map_mul _ f' f

private theorem conjQuotAction_range_sq (F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y)
    (hQker : ∀ q : ↥F, q ∈ Q.subgroupOf F →
      q ∈ (conjQuotAction F Y Q hFN hQinv).ker)
    (hsq : ∀ f ∈ F, (f : G) ^ 2 ∈ Q) :
    ∀ a ∈ (conjQuotAction F Y Q hFN hQinv).range, a * a = 1 := by
  rintro _ ⟨f, rfl⟩
  let qF : ↥F := f * f
  have hqF : qF ∈ Q.subgroupOf F := by
    change ((f : G) * (f : G)) ∈ Q
    have h := hsq f f.2
    rwa [pow_two] at h
  calc conjQuotAction F Y Q hFN hQinv f * conjQuotAction F Y Q hFN hQinv f
      = conjQuotAction F Y Q hFN hQinv (f * f) := (map_mul _ f f).symm
    _ = conjQuotAction F Y Q hFN hQinv qF := rfl
    _ = 1 := MonoidHom.mem_ker.mp (hQker qF hqF)

private noncomputable def conjQuotActionCongr (F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y)
    {R : Type} [Group R] (e : (↥Y ⧸ Q.subgroupOf Y) ≃* R) : ↥F →* MulAut R :=
  (MulAut.congr e).toMonoidHom.comp (conjQuotAction F Y Q hFN hQinv)

private theorem conjQuotActionCongr_range_comm (F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y)
    {R : Type} [Group R] (e : (↥Y ⧸ Q.subgroupOf Y) ≃* R)
    (hQker : ∀ q : ↥F, q ∈ Q.subgroupOf F →
      q ∈ (conjQuotAction F Y Q hFN hQinv).ker)
    (hcomm : ∀ f ∈ F, ∀ f' ∈ F, ⁅(f : G), (f' : G)⁆ ∈ Q) :
    ∀ a ∈ (conjQuotActionCongr F Y Q hFN hQinv e).range,
      ∀ b ∈ (conjQuotActionCongr F Y Q hFN hQinv e).range, a * b = b * a := by
  have h := conjQuotAction_range_comm F Y Q hFN hQinv hQker hcomm
  rintro _ ⟨f, rfl⟩ _ ⟨f', rfl⟩
  calc (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f) *
        (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f')
      = (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f *
          conjQuotAction F Y Q hFN hQinv f') := (map_mul _ _ _).symm
    _ = (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f' *
          conjQuotAction F Y Q hFN hQinv f) := by
      rw [h (conjQuotAction F Y Q hFN hQinv f) ⟨f, rfl⟩
        (conjQuotAction F Y Q hFN hQinv f') ⟨f', rfl⟩]
    _ = (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f') *
        (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f) := map_mul _ _ _

private theorem conjQuotActionCongr_range_sq (F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y)
    {R : Type} [Group R] (e : (↥Y ⧸ Q.subgroupOf Y) ≃* R)
    (hQker : ∀ q : ↥F, q ∈ Q.subgroupOf F →
      q ∈ (conjQuotAction F Y Q hFN hQinv).ker)
    (hsq : ∀ f ∈ F, (f : G) ^ 2 ∈ Q) :
    ∀ a ∈ (conjQuotActionCongr F Y Q hFN hQinv e).range, a * a = 1 := by
  have h := conjQuotAction_range_sq F Y Q hFN hQinv hQker hsq
  rintro _ ⟨f, rfl⟩
  calc (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f) *
        (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f)
      = (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f *
          conjQuotAction F Y Q hFN hQinv f) := (map_mul _ _ _).symm
    _ = (MulAut.congr e) 1 := by
      rw [h (conjQuotAction F Y Q hFN hQinv f) ⟨f, rfl⟩]
    _ = 1 := map_one _

private theorem conjQuotActionCongr_ker_spec (F Y Q : Subgroup G)
    (hFN : F ≤ Subgroup.normalizer (Y : Set G)) [hQn : (Q.subgroupOf Y).Normal]
    (hQinv : ∀ f : ↥F,
      (Q.subgroupOf Y).map ((conjAction F Y hFN f).toMonoidHom) = Q.subgroupOf Y)
    {R : Type} [Group R] (e : (↥Y ⧸ Q.subgroupOf Y) ≃* R) (f : ↥F)
    (hf : f ∈ (conjQuotActionCongr F Y Q hFN hQinv e).ker) :
    ∀ y ∈ Y, ⁅(f : G), y⁆ ∈ Q := by
  have h2 : conjQuotAction F Y Q hFN hQinv f = 1 := by
    have h3 : (MulAut.congr e) (conjQuotAction F Y Q hFN hQinv f) = (MulAut.congr e) 1 := by
      rw [map_one]
      simpa [conjQuotActionCongr] using MonoidHom.mem_ker.mp hf
    exact (MulAut.congr e).injective h3
  intro y hy
  exact (conjQuotAction_ker_iff F Y Q hFN hQinv f).mp h2 ⟨y, hy⟩

private theorem exists_mem_conj_comm_not_mem_Q (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y)
    (h1 : OneConcl hc X Y) {g : G} (hg : g ∈ M)
    (hcommQ : ∀ f ∈ conjSubgroup g (LB M Q B ⊓ X), ∀ e ∈ LB M Q B ⊓ X, ⁅f, e⁆ ∈ Q) :
    ∃ f ∈ conjSubgroup g (LB M Q B ⊓ X), f ∉ Q ∧ ∀ y ∈ Y, ⁅f, y⁆ ∈ Q := by
  classical
  have hsplit0 := hsplit
  obtain ⟨e₀, he₀, he₀Q⟩ := exists_mem_inf_not_mem_Q h34 hc hs hsplit h4
  have hFN := conjSubgroup_le_normalizer hc hsplit0 h1 hg he₀ he₀Q hcommQ
  obtain ⟨⟨hQX, -, -, hYR, -, -, -⟩, hYsl, -⟩ := hsplit
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hQM : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := fun m hm q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQn hm) q).mp hq
  have hYM : Y ≤ M := hYR.trans (hc.Rt_le_M t)
  let F : Subgroup G := conjSubgroup g (LB M Q B ⊓ X)
  have hFM : F ≤ M := conjSubgroup_le_M hc hg
  have hQF : Q ≤ F := by
    intro q hq
    have h0 : g⁻¹ * q * g ∈ Q := by
      have h := hQM (g : G)⁻¹ (M.inv_mem hg) (q : G) hq
      simpa using h
    exact mem_conjSubgroup.mpr ⟨Subgroup.mem_sup_left h0, hQX h0⟩
  haveI hQYn : (Q.subgroupOf Y).Normal := hYsl.1
  obtain ⟨K, hKfield, hKfin, hKq, heK⟩ := hYsl.2
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨eK⟩ := heK
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card Z = 2 ^ k := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hk)
  let eSL : (↥Y ⧸ Q.subgroupOf Y) ≃* SpecialLinearGroup (Fin 2) K :=
    eK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  have hQinv := conjAction_quotient_invariant M F Y Q hFN hFM hQM
  let ψ : ↥F →* MulAut (SpecialLinearGroup (Fin 2) K) :=
    conjQuotActionCongr F Y Q hFN hQinv eSL
  have hQkerQ : ∀ q : ↥F, q ∈ Q.subgroupOf F →
      q ∈ (conjQuotAction F Y Q hFN hQinv).ker := fun q hq =>
    conjQuotAction_q_mem_ker M F Y Q hFN hQinv hQM hYM q hq
  have hQker : ∀ q : ↥F, q ∈ Q.subgroupOf F → q ∈ ψ.ker := by
    intro q hq
    change ψ q = 1
    change (MulAut.congr eSL) (conjQuotAction F Y Q hFN hQinv q) = 1
    rw [MonoidHom.mem_ker.mp (hQkerQ q hq), map_one]
  have hrange_comm := conjQuotActionCongr_range_comm F Y Q hFN hQinv eSL hQkerQ
    (fun f hf f' hf' => commutator_mem_Q_of_mem_conj hc hg hf hf')
  have hrange_sq := conjQuotActionCongr_range_sq F Y Q hFN hQinv eSL hQkerQ
    (fun f hf => sq_mem_Q_of_mem_conj hc hg hf)
  have hcard_range : Nat.card ψ.range ≤ Nat.card K := by
    have hs1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exfalso
        rw [h, pow_zero] at hk
        have := hc.hyp.q4
        omega
      · exact h
    exact CFSG.Quasithin.Vol2.Ch10.SecD.C10P06.card_le_of_elem_aut
      (n := k) (hKq.trans hk) hs1 hrange_comm hrange_sq
  have hcardF : Nat.card ↥F = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hcardE : Nat.card ↥F = Nat.card ↥(LB M Q B ⊓ X) := by
    change Nat.card ↥(conjSubgroup g (LB M Q B ⊓ X)) = _
    exact card_conjSubgroup g _
  have hge := card_inf_ge hc hs hsplit0 h4
  have hn4 := HS6.four_le_of_omegaPlus_two h34 hc hs.toSec5 hs.plus4
  obtain ⟨f, hfker, hfQ⟩ := exists_mem_ker_not_mem (Z := Z) (n := n) (X := X)
    (F := F) ψ (hcard_range.trans (le_of_eq hKq)) hcardF hcardE hge hn4 hc.hyp.q4 hQF
  have hker_spec := conjQuotActionCongr_ker_spec F Y Q hFN hQinv eSL f hfker
  refine ⟨(f : G), f.2, ?_, hker_spec⟩
  intro hfq
  exact hfQ (Subgroup.mem_subgroupOf.mpr hfq)

private theorem comm_LB_mem_Q_of_comm_Y (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {f : G}
    (hcommE : ∀ e ∈ LB M Q B ⊓ X, ⁅f, e⁆ ∈ Q)
    (hcommY : ∀ y ∈ Y, ⁅f, y⁆ ∈ Q) :
    ∀ l ∈ LB M Q B, ⁅f, l⁆ ∈ Q := by
  obtain ⟨⟨-, -, hQY, -, -, -, hcXY⟩, -, -⟩ := hsplit
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hQM : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := fun m hm q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQn hm) q).mp hq
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQEY : Q ≤ LB M Q B ⊓ Y := le_inf hQL hQY
  have hnorm : (LB M Q B ⊓ X) ≤
      Subgroup.normalizer ((LB M Q B ⊓ Y : Subgroup G) : Set G) :=
    HS9.normalizer_of_commutator_le (X := LB M Q B ⊓ Y) (Y := LB M Q B ⊓ X) hQEY
      fun a ha y hy => by
        have h := Q.inv_mem (hcXY y hy.2 a ha.2)
        rwa [commutatorElement_inv] at h
  intro l hl
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer hnorm (h4.2.2 ▸ hl)
  rw [← hab, commutatorElement_mul_right_eq_mul_conj]
  have haQ : ⁅f, a⁆ ∈ Q := hcommE a ha
  have hbQ : ⁅f, b⁆ ∈ Q := hcommY b hb.2
  have hconj : a * ⁅f, b⁆ * a⁻¹ ∈ Q := hQM a (hc.LB_le_M ha.1) _ hbQ
  rw [show ⁅f, a⁆ * a * ⁅f, b⁆ * a⁻¹ = ⁅f, a⁆ * (a * ⁅f, b⁆ * a⁻¹) by group]
  exact Q.mul_mem haQ hconj

private theorem mem_LB_of_comm_LB (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X : Subgroup G} {g f : G} (hg : g ∈ M)
    (hf : f ∈ conjSubgroup g (LB M Q B ⊓ X))
    (hcomm : ∀ l ∈ LB M Q B, ⁅f, l⁆ ∈ Q) : f ∈ LB M Q B := by
  classical
  haveI hQn : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  let A : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  have hApg : IsPGroup 2 A := hc.isElemAbelian_bar_LB.isPGroup
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hw : CFSG.LargeExtraspecial.IsWeaklyClosedInNormalizer A := by
    intro x hx
    change conjSubgroup x A = A
    exact hc.weaklyClosed_bar_LB hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 x hx
  have hstrong := CFSG.LargeExtraspecial.lemma_3_12_isStronglyClosedIn (p := 2) hApg hAc hw
  have he : g⁻¹ * f * g ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hf
  have hfM : f ∈ M := conjSubgroup_le_M hc hg hf
  let a : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) ⟨g⁻¹ * f * g, hc.LB_le_M he.1⟩
  let x : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) ⟨g⁻¹, M.inv_mem hg⟩
  have ha : a ∈ A := (mk_mem_bar_iff_sec4 sec39_Q_le_LB _).mpr he.1
  have hxconj : x⁻¹ * a * x = QuotientGroup.mk' (Q.subgroupOf M) ⟨f, hfM⟩ := by
    change (QuotientGroup.mk' (Q.subgroupOf M) ⟨g⁻¹, M.inv_mem hg⟩)⁻¹ *
      QuotientGroup.mk' (Q.subgroupOf M) ⟨g⁻¹ * f * g, hc.LB_le_M he.1⟩ *
      QuotientGroup.mk' (Q.subgroupOf M) ⟨g⁻¹, M.inv_mem hg⟩ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hfcent : QuotientGroup.mk' (Q.subgroupOf M) ⟨f, hfM⟩ ∈
      Subgroup.centralizer (A : Set (Mbar M Q)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_mul, ← map_mul, QuotientGroup.coe_mk']
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have e : (((l * ⟨f, hfM⟩) / (⟨f, hfM⟩ * l) : ↥M) : G) = ⁅(l : G), f⁆ := by
      simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [div_eq_mul_inv, commutatorElement_def]
      group
    rw [e]
    have h := hcomm (l : G) hl
    have h' : ⁅(l : G), f⁆ ∈ Q := by
      have h2 := Q.inv_mem h
      rwa [commutatorElement_inv] at h2
    exact h'
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨f, hfM⟩ ∈ A := by
    have hcent : x⁻¹ * a * x ∈ Subgroup.centralizer (A : Set (Mbar M Q)) := by
      rw [hxconj]
      exact hfcent
    have hmemA : x⁻¹ * a * x ∈ A := hstrong.2 a ha x hcent
    rwa [hxconj] at hmemA
  exact (mk_mem_bar_iff_sec4 sec39_Q_le_LB ⟨f, hfM⟩).mp hmem

theorem sec97ThreeCaseB_of (h34 : Stroth34Statement) : Sec97ThreeCaseB := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 h1 _ g hg hF hcommQ
  obtain ⟨f, hfF, hfQ, hfY⟩ :=
    exists_mem_conj_comm_not_mem_Q h34 hc hs hsplit h4 h1 hg hcommQ
  have hfM : f ∈ M := conjSubgroup_le_M hc hg hfF
  have hcommE : ∀ e ∈ LB M Q B ⊓ X, ⁅f, e⁆ ∈ Q := fun e he => hcommQ f hfF e he
  have hcommLB : ∀ l ∈ LB M Q B, ⁅f, l⁆ ∈ Q :=
    comm_LB_mem_Q_of_comm_Y hc hsplit h4 hcommE hfY
  have hfLB : f ∈ LB M Q B := mem_LB_of_comm_LB hc hs hg hfF hcommLB
  have hfX : f ∈ X := HS9.mem_X_of_comm_mem_Q hc hsplit h4 hfLB hfY
  exact hfQ (hF ⟨hfF, hfLB, hfX⟩)

end CFSG.RankThree.GF2n.Stroth80
