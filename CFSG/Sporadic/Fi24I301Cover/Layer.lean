module

public import CFSG.Sporadic.Fi24I301.Layer
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusThree
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Grp
import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component

public section

namespace CFSG.Sporadic.Fi24I301Cover

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

section Split

open CFSG.LieType.Universal

theorem exists_section_of_statedPOmegaPlus_three {E : Type*} {N : Type} [Group E] [Group N]
    (π : E →* N) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    (hodd : ¬ 2 ∣ Nat.card π.ker) (hN : StatedClassicalModel N .POmegaPlus 4 3 1) :
    ∃ σ : N →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨θ⟩⟩ := hN
  let _ := hfield
  let _ := hfinite
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hq, hkerS, -⟩ := Spin.spinToStatedProj_quadPlus (K := K) hn3
  set q := Spin.spinToStatedProj (Spin.quadPlus 4 K) (Spin.range_spinMatrix_quadPlus hn3)
    with hqdef
  let f₁ : E × spinGroup (Spin.quadPlus 4 K) →* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (θ.toMonoidHom.comp π).comp (MonoidHom.fst _ _)
  let f₂ : E × spinGroup (Spin.quadPlus 4 K) →* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    q.comp (MonoidHom.snd _ _)
  let P : Subgroup (E × spinGroup (Spin.quadPlus 4 K)) := f₁.eqLocus f₂
  let p₂ : ↥P →* spinGroup (Spin.quadPlus 4 K) := (MonoidHom.snd _ _).comp P.subtype
  have hp₂ : Function.Surjective p₂ := by
    intro s
    obtain ⟨e, he⟩ := hπ (θ.symm (q s))
    refine ⟨⟨(e, s), ?_⟩, rfl⟩
    show θ (π e) = q s
    rw [he, MulEquiv.apply_symm_apply]
  have hcen : p₂.ker ≤ Subgroup.center ↥P := by
    rintro ⟨⟨e, s⟩, hes⟩ hx
    have hs1 : s = 1 := hx
    have he : π e = 1 := by
      have h : θ (π e) = q s := hes
      rw [hs1, map_one] at h
      exact θ.injective (h.trans (map_one θ).symm)
    have hez := Subgroup.mem_center_iff.mp (hker he)
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨e', s'⟩, -⟩
    apply Subtype.ext
    show (e' * e, s' * s) = (e * e', s * s')
    rw [hs1, mul_one, one_mul, hez e']
  obtain ⟨σ₀, hσ₀⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_three_exists_section_of_central
      hn3 hK3 le_rfl hp₂ hcen
  let τ : spinGroup (Spin.quadPlus 4 K) →* E := (MonoidHom.fst _ _).comp (P.subtype.comp σ₀)
  have hτ : ∀ s, θ (π (τ s)) = q s := by
    intro s
    have h1 : f₁ (σ₀ s) = f₂ (σ₀ s) := (σ₀ s).2
    have h2 : (σ₀ s : E × spinGroup (Spin.quadPlus 4 K)).2 = s := hσ₀ s
    calc θ (π (τ s)) = f₁ (σ₀ s) := rfl
      _ = f₂ (σ₀ s) := h1
      _ = q s := by
        show q (σ₀ s : E × spinGroup (Spin.quadPlus 4 K)).2 = q s
        rw [h2]
  have hτZ : q.ker ≤ τ.ker := by
    intro x hx
    have hxS : x ∈ (StatedScalars _ K).comap (Spin.spinMatrix (Spin.quadPlus 4 K)) := by
      rw [← hkerS]
      exact hx
    obtain ⟨c, hc⟩ := Subgroup.mem_comap.mp hxS
    have hc2 : c ^ 2 = 1 := by
      have h := pow_card_eq_one' (x := c)
      rw [Nat.card_units, hK3] at h
      simpa using h
    have hx2 : x ^ 2 ∈ (Spin.spinMatrix (Spin.quadPlus 4 K)).ker := by
      rw [MonoidHom.mem_ker, map_pow, ← hc, ← map_pow, hc2, map_one]
    have hx4 : x ^ 2 * x ^ 2 = 1 :=
      CFSG.ClassicalInvolution.ModelFacts.OrthAut.spin_mul_self_eq_one
        ((Spin.mem_ker_spinMatrix_quadPlus_iff _).mp hx2)
    have hx4' : x ^ 4 = 1 :=
      calc x ^ 4 = x ^ 2 * x ^ 2 := by group
        _ = 1 := hx4
    have hτ4 : τ x ^ 4 = 1 := by
      rw [← map_pow, hx4', map_one]
    have hτx : τ x ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      apply θ.injective
      rw [hτ x, map_one]
      exact MonoidHom.mem_ker.mp hx
    have hcop : Nat.Coprime 4 (Nat.card π.ker) := by
      have h2 : Nat.Coprime 2 (Nat.card π.ker) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
      simpa using Nat.Coprime.pow_left 2 h2
    have hord : orderOf (τ x) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hτ4) hcop)
        (π.ker.orderOf_dvd_natCard hτx)
    exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp hord)
  let eK := QuotientGroup.quotientKerEquivOfSurjective q hq
  refine ⟨(QuotientGroup.lift q.ker τ hτZ).comp (eK.symm.toMonoidHom.comp θ.toMonoidHom),
    fun g => ?_⟩
  obtain ⟨s, hs⟩ := hq (θ g)
  have h1 : eK.symm (θ g) = (s : spinGroup (Spin.quadPlus 4 K) ⧸ q.ker) :=
    (MulEquiv.symm_apply_eq eK).2 (hs.symm.trans rfl)
  apply θ.injective
  show θ (π (QuotientGroup.lift q.ker τ hτZ (eK.symm (θ g)))) = θ g
  rw [h1, QuotientGroup.lift_mk, hτ, hs]

end Split

section Layer

private theorem isPerfect_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect S := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    refine absurd ?_ hab
    rw [← commutatorElement_eq_one_iff_mul_comm, ← Subgroup.mem_bot, ← h, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  · exact h

variable {E : Type} [Group E] [Finite E]

theorem glaPLayer_eq_of_isSimple_normal_commutator_le_sup {p : ℕ} (hp : p.Prime)
    {H S A : Subgroup E} (hSH : S ≤ H) (hSn : ∀ g ∈ H, ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (hS : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hpS : p ∣ Nat.card ↥S)
    (hA : A ≤ Subgroup.center E) (hc : ⁅H, H⁆ ≤ S ⊔ A) : GLAPLayer p H = S := by
  haveI := hS
  have hn : (S.subgroupOf H).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hSn g.1 g.2 x hx⟩
  have hcomp : GLAPComponent p H S :=
    GL83.PiGen.glaPComponent_of_normal_simple hp hSH hn hnab hpS
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b _ =>
    (Subgroup.mem_center_iff.mp (hA ha) b).symm
  have hAS : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := fun a ha s hs => by
    rw [← Subgroup.mem_center_iff.mp (hA ha) s, mul_inv_cancel_right]
    exact hs
  unfold GLAPLayer
  refine le_antisymm (sSup_le fun K hK => ?_) (le_sSup hcomp)
  have hK' : GLAPComponent p H K := hK
  have hKK : ⁅K, K⁆ = K := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hK'
  have hKle : K ≤ S ⊔ A := by
    rw [← hKK]
    exact (Subgroup.commutator_mono hK'.1 hK'.1).trans hc
  rw [← hKK]
  exact H301.commutator_le_of_le_sup_of_commute hKle hAc hAS

theorem glaPLayer_centralizer_eq_range_of_section {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (π : E →* G) (hker : π.ker ≤ Subgroup.center E) {s : G} {L : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({s} : Set G))
    (hLn : ∀ g ∈ Subgroup.centralizer ({s} : Set G), ∀ x ∈ L, g * x * g⁻¹ ∈ L)
    (hc : ⁅Subgroup.centralizer ({s} : Set G), Subgroup.centralizer ({s} : Set G)⁆ ≤ L)
    (hL : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    (σ : ↥L →* E) (hσ : ∀ g, π (σ g) = g) {ŝ : E} (hs : π ŝ = s) :
    GLAPLayer p (Subgroup.centralizer ({ŝ} : Set E)) = σ.range := by
  haveI := hL
  have hσinj : Function.Injective σ := fun a b h =>
    Subtype.ext ((hσ a).symm.trans ((congrArg π h).trans (hσ b)))
  let eS : ↥L ≃* ↥σ.range := MonoidHom.ofInjective hσinj
  haveI : Group.IsPerfect ↥L := isPerfect_of_isSimpleGroup hnab
  haveI : Group.IsPerfect ↥σ.range := Group.IsPerfect.range σ
  have hperf : ⁅σ.range, σ.range⁆ = σ.range := Subgroup.commutator_eq_self
  have hHs : ∀ h ∈ Subgroup.centralizer ({ŝ} : Set E),
      π h ∈ Subgroup.centralizer ({s} : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
    rw [← hs, ← map_mul, hh, map_mul]
  have hSP : σ.range ≤ L.comap π := by
    rintro _ ⟨g, rfl⟩
    show π (σ g) ∈ L
    rw [hσ]
    exact g.2
  have hPS : L.comap π ≤ σ.range ⊔ π.ker := by
    intro x hx
    have h1 : σ ⟨π x, hx⟩ ∈ σ.range := ⟨_, rfl⟩
    have h2 : (σ ⟨π x, hx⟩)⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]
      exact inv_mul_cancel _
    have h3 := Subgroup.mul_mem_sup h1 h2
    rwa [mul_inv_cancel_left] at h3
  have hAc : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a := fun a ha b _ =>
    (Subgroup.mem_center_iff.mp (hker ha) b).symm
  have hAS : ∀ a ∈ π.ker, ∀ x ∈ σ.range, a * x * a⁻¹ ∈ σ.range := fun a ha x hx => by
    rw [← Subgroup.mem_center_iff.mp (hker ha) x, mul_inv_cancel_right]
    exact hx
  have hSeq : σ.range = ⁅L.comap π, L.comap π⁆ := by
    refine le_antisymm ?_ (H301.commutator_le_of_le_sup_of_commute hPS hAc hAS)
    have h := Subgroup.commutator_mono hSP hSP
    rwa [hperf] at h
  have hSn : ∀ h ∈ Subgroup.centralizer ({ŝ} : Set E), ∀ x ∈ σ.range,
      h * x * h⁻¹ ∈ σ.range := by
    intro h hh x hx
    rw [hSeq] at hx ⊢
    have hPm : (L.comap π).map (MulAut.conj h).toMonoidHom ≤ L.comap π := by
      rintro _ ⟨y, hy, rfl⟩
      show π (h * y * h⁻¹) ∈ L
      rw [map_mul, map_mul, map_inv]
      exact hLn _ (hHs h hh) _ hy
    have hmap : (⁅L.comap π, L.comap π⁆).map (MulAut.conj h).toMonoidHom ≤
        ⁅L.comap π, L.comap π⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hPm hPm
    exact hmap ⟨x, hx, rfl⟩
  have hSH : σ.range ≤ Subgroup.centralizer ({ŝ} : Set E) := by
    have hcen : ∀ x : ↥σ.range, (((MulAut.conj ŝ).toMonoidHom.comp σ.range.subtype) x)⁻¹ *
        σ.range.subtype x ∈ Subgroup.center E := by
      rintro ⟨x, hx⟩
      apply hker
      have hxs : π x * s = s * π x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hLC (hSP hx))
      have hconj : π (ŝ * x * ŝ⁻¹) = π x := by
        rw [map_mul, map_mul, map_inv, hs, ← hxs, mul_inv_cancel_right]
      show π ((ŝ * x * ŝ⁻¹)⁻¹ * x) = 1
      rw [map_mul, map_inv, hconj, inv_mul_cancel]
    have heq := CFSG.ClassicalInvolution.ModelFacts.OrthAut.eq_of_inv_mul_mem_center
      σ.range.subtype ((MulAut.conj ŝ).toMonoidHom.comp σ.range.subtype) hcen
    intro x hx
    have h1 : ŝ * x * ŝ⁻¹ = x := DFunLike.congr_fun heq ⟨x, hx⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * ŝ = ŝ * x * ŝ⁻¹ * ŝ := by rw [h1]
      _ = ŝ * x := by group
  have hcH : ⁅Subgroup.centralizer ({ŝ} : Set E), Subgroup.centralizer ({ŝ} : Set E)⁆ ≤
      σ.range ⊔ π.ker := by
    refine le_trans ?_ hPS
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
    have hHm : (Subgroup.centralizer ({ŝ} : Set E)).map π ≤
        Subgroup.centralizer ({s} : Set G) := by
      rintro _ ⟨h, hh, rfl⟩
      exact hHs h hh
    exact (Subgroup.commutator_mono hHm hHm).trans hc
  obtain ⟨a, b, hab⟩ := hnab
  exact glaPLayer_eq_of_isSimple_normal_commutator_le_sup hp hSH hSn
    (eS.isSimpleGroup_congr.1 hL)
    ⟨eS a, eS b, fun h => hab (eS.injective (by rw [map_mul, map_mul, h]))⟩
    (by rw [← Nat.card_congr eS.toEquiv]; exact hpL) hker hcH

theorem isTypeWithCenter_centralizer_of_section {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (π : E →* G) (hker : π.ker ≤ Subgroup.center E) {s : G} {L : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({s} : Set G))
    (hLn : ∀ g ∈ Subgroup.centralizer ({s} : Set G), ∀ x ∈ L, g * x * g⁻¹ ∈ L)
    (hc : ⁅Subgroup.centralizer ({s} : Set G), Subgroup.centralizer ({s} : Set G)⁆ ≤ L)
    (hL : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    {Q : TauCeti.CFSGIndex → Prop} (hQ : catalogIs ↥L Q) (σ : ↥L →* E)
    (hσ : ∀ g, π (σ g) = g) {ŝ : E} (hs : π ŝ = s) :
    IsTypeWithCenter p (GLAPLayer p (Subgroup.centralizer ({ŝ} : Set E))) Q 1 := by
  rw [glaPLayer_centralizer_eq_range_of_section hp π hker hLC hLn hc hL hnab hpL σ hσ hs]
  have hσinj : Function.Injective σ := fun a b h =>
    Subtype.ext ((hσ a).symm.trans ((congrArg π h).trans (hσ b)))
  let eS : ↥L ≃* ↥σ.range := MonoidHom.ofInjective hσinj
  obtain ⟨i, hi, ⟨f⟩⟩ := hQ
  obtain ⟨a, b, hab⟩ := hnab
  exact H301.isTypeWithCenter_of_isSimple hp (eS.isSimpleGroup_congr.1 hL)
    ⟨eS a, eS b, fun h => hab (eS.injective (by rw [map_mul, map_mul, h]))⟩
    (by rw [← Nat.card_congr eS.toEquiv]; exact hpL) ⟨i, hi, ⟨eS.symm.trans f⟩⟩

end Layer

section PIndex

variable {G : Type} [Group G] [Finite G]

theorem normal_commutator_le_of_isSimple_index_sq {p : ℕ} (hp : p.Prime) {C L : Subgroup G}
    (hLC : L ≤ C) (hs : IsSimpleGroup ↥L) (hk : Nat.card ↥C = Nat.card ↥L * p ^ 2)
    (hfac : (p ^ 2).factorial < Nat.card ↥C) :
    (∀ g ∈ C, ∀ x ∈ L, g * x * g⁻¹ ∈ L) ∧ ⁅C, C⁆ ≤ L := by
  haveI : Fact p.Prime := ⟨hp⟩
  let E : Subgroup ↥C := L.subgroupOf C
  have eL : ↥E ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  haveI : IsSimpleGroup ↥E := eL.isSimpleGroup_congr.2 hs
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  have hidx : E.index = p ^ 2 := by
    have h1 : E.index * Nat.card ↥E = Nat.card ↥C := Subgroup.index_mul_card E
    rw [Nat.card_congr eL.toEquiv, hk] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])
  haveI hEn : E.Normal := CFSG.HardMathSupport.Dickson.I271.normal_of_isSimple_of_index E hidx
    (pow_ne_zero 2 hp.ne_zero) hfac
  refine ⟨fun g hg x hx => Subgroup.mem_subgroupOf.1
    (hEn.conj_mem ⟨x, hLC hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨g, hg⟩), ?_⟩
  have hq : Nat.card (↥C ⧸ E) = p ^ 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hab := IsPGroup.commutative_of_card_eq_prime_sq hq
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have h1 : (QuotientGroup.mk ((⟨a, ha⟩ : ↥C) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥C)⁻¹ *
      (⟨b, hb⟩ : ↥C)⁻¹) : ↥C ⧸ E) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hab (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)]
    group
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

end PIndex

section Recognition

open CFSG.Timmesfeld CFSG.ClassicalInvolution.Q3.Q3Z CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Blueprint CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Dickson.I271

theorem statedClassicalModel_d4Group {Y : Type} [Group Y] (x y : Fin 4 → Y)
    (hrel : ∀ a b : Fin 4, edgeD 4 a b → RelsHold (edgeSix (x a) (y a) (x b) (y b)) a2Words)
    (hne : ∀ a b : Fin 4, edgeD 4 a b → x a ≠ 1)
    (hcomm : ∀ a b : Fin 4, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a →
      ∀ u ∈ ({x a, y a} : Set Y), ∀ v ∈ ({x b, y b} : Set Y), u * v = v * u)
    (hdvd : Nat.card (d4Group x y) ∣ 3 * 4952179814400) :
    StatedClassicalModel ↥(d4Group x y) .POmegaPlus 4 3 1 := by
  set U : Fin 4 → Subgroup Y := fun a => Subgroup.closure ({x a, y a} : Set Y) with hU
  set N : Subgroup Y := d4Group x y with hNdef
  have hUN : ∀ a, U a ≤ N := fun a => le_iSup U a
  have hgen : ⨆ a, (U a).subgroupOf N = ⊤ :=
    CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self U
  have hcomm' : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
      ∀ a ∈ (U i).subgroupOf N, ∀ b ∈ (U j).subgroupOf N, a * b = b * a := by
    intro i j hij h1 h2 a ha b hb
    exact Subtype.ext (d4_closure_commute (hcomm i j hij h1 h2) a.1 ha b.1 hb)
  haveI hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e3⟩ := d4_ringEq
  have hpair : ∀ i j : Fin 4, edgeD 4 i j → ∃ W, LinearBlockStandardPair (GaloisField 3 1) W
      ((U i).subgroupOf N) ((U j).subgroupOf N) := by
    intro i j hij
    have h := linearBlockStandardPair_of_relsHold (edgeSix (x i) (y i) (x j) (y j))
      (hrel i j hij) (hne i j hij)
    have h' := LinearBlockStandardPair.of_ringEquiv e3 h
    have h'' : LinearBlockStandardPair (GaloisField 3 1)
        (Subgroup.closure (Set.range (edgeSix (x i) (y i) (x j) (y j)))) (U i) (U j) := h'
    exact ⟨_, CFSG.GH74.L5U5.linearBlockStandardPair_subgroupOf h'' N (hUN i) (hUN j)⟩
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    simpa using GaloisField.card 3 1 (by norm_num)
  obtain ⟨Ψ, -, -, -, hZ, hmodel, -⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3W.weakCT3_spinPlus hadm (by norm_num : 3 ≤ 4) hF
      (X := ↥N) (fun a => (U a).subgroupOf N) hgen hcomm' hpair
  have hcz : Nat.card (Subgroup.center ↥N) ∣
      Nat.card (Subgroup.center (spinGroup (Spin.quadPlus 4 (GaloisField 3 1)))) := by
    rw [hZ]
    exact Subgroup.card_map_dvd _ Ψ
  have hquot : Nat.card (↥N ⧸ Subgroup.center ↥N) = 4952179814400 := d4_card_pomegaPlus hmodel
  have hcardN : Nat.card ↥N = 4952179814400 * Nat.card (Subgroup.center ↥N) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥N), hquot]
  have hZdvd3 : Nat.card (Subgroup.center ↥N) ∣ 3 := by
    have h1 : 4952179814400 * Nat.card (Subgroup.center ↥N) ∣ 4952179814400 * 3 := by
      rw [← hcardN, mul_comm 4952179814400 3]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hZ1 : Nat.card (Subgroup.center ↥N) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZdvd3 with h | h
    · exact h
    · exfalso
      rw [h] at hcz
      exact d4_center_spin_not_dvd hcz
  have hZbot : Subgroup.center ↥N = ⊥ := Subgroup.card_eq_one.1 hZ1
  let eN : (↥N ⧸ Subgroup.center ↥N) ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eN
    (hmodel.statedClassicalModel_of_ne_zero (by norm_num))

end Recognition

section Fi24

open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabFi24
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three (fi24Rep3)
open CFSG.Sporadic.Fi24 (J)

theorem statedClassicalModel_fiN : StatedClassicalModel ↥fiN .POmegaPlus 4 3 1 := by
  refine statedClassicalModel_d4Group dx dy d4_hrel d4_hne d4_hcomm ?_
  have h := Subgroup.card_dvd_of_le fiN_le_lvl_two
  rw [card_lvl_two] at h
  simpa using h

theorem fiN_normal_commutator_le :
    (∀ g ∈ cent0, ∀ x ∈ fiN, g * x * g⁻¹ ∈ fiN) ∧ ⁅cent0, cent0⁆ ≤ fiN := by
  obtain ⟨hcard, hsimple, -, -⟩ := fiN_facts
  refine normal_commutator_le_of_isSimple_index_sq Nat.prime_three
    (fiN_le_lvl_two.trans lvl_two_le_cent0) hsimple ?_ ?_
  · rw [card_cent0, hcard]
    norm_num
  · rw [card_cent0]
    decide

variable {E : Type} [Group E]

theorem exists_section_fiN (π : E →* J) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (hodd : ¬ 2 ∣ Nat.card π.ker) :
    ∃ σ : ↥fiN →* E, ∀ g, π (σ g) = g := by
  let πP : ↥(fiN.comap π) →* ↥fiN :=
    (π.comp (fiN.comap π).subtype).codRestrict fiN fun x => x.2
  have hπP : Function.Surjective πP := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := hπ y
    exact ⟨⟨e, hy⟩, rfl⟩
  have hkerP : πP.ker ≤ Subgroup.center ↥(fiN.comap π) := by
    intro x hx
    have hx1 : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxz := Subgroup.mem_center_iff.mp (hker hx1)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hxz y)
  have hoddP : ¬ 2 ∣ Nat.card πP.ker := by
    intro h2
    apply hodd
    have hle : πP.ker.map (fiN.comap π).subtype ≤ π.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (fiN.comap π).subtype_injective] at h
    exact h2.trans h
  obtain ⟨σ, hσ⟩ := exists_section_of_statedPOmegaPlus_three πP hπP hkerP hoddP
    statedClassicalModel_fiN
  exact ⟨(fiN.comap π).subtype.comp σ, fun g => congrArg Subtype.val (hσ g)⟩

variable [Finite E]

theorem isTypeWithCenter_layer_cover_s0 (π : E →* J) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (hodd : ¬ 2 ∣ Nat.card π.ker) {ŝ : E} (hs : π ŝ = s0) :
    IsTypeWithCenter 3 (GLAPLayer 3 (Subgroup.centralizer ({ŝ} : Set E))) (isD4of 3) 1 := by
  obtain ⟨hcard, hsimple, hnab, -⟩ := fiN_facts
  obtain ⟨hNn, hcomm⟩ := fiN_normal_commutator_le
  obtain ⟨σ, hσ⟩ := exists_section_fiN π hπ hker hodd
  exact isTypeWithCenter_centralizer_of_section Nat.prime_three π hker
    (fiN_le_lvl_two.trans lvl_two_le_cent0) hNn hcomm hsimple hnab (by rw [hcard]; norm_num)
    catalogIs_fiN σ hσ hs

theorem isTypeWithCenter_layer_cover_rep0 (π : E →* J) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (hodd : ¬ 2 ∣ Nat.card π.ker) {ŝ : E}
    (hs : π ŝ = fi24Rep3 0) :
    IsTypeWithCenter 3 (GLAPLayer 3 (Subgroup.centralizer ({ŝ} : Set E))) (isD4of 3) 1 := by
  have hconj : IsConj s0 (fi24Rep3 0) := isConj_rep0_s0.symm
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨ĉ, rfl⟩ := hπ c
  have hs0 : π (ĉ⁻¹ * ŝ * ĉ) = s0 := by
    rw [map_mul, map_mul, map_inv, hs, ← hc]
    group
  have hĉ : IsConj (ĉ⁻¹ * ŝ * ĉ) ŝ := isConj_iff.2 ⟨ĉ, by group⟩
  exact Fi24I301.isTypeWithCenter_glaPLayer_centralizer_of_isConj hĉ
    (isTypeWithCenter_layer_cover_s0 π hπ hker hodd hs0)

end Fi24

end CFSG.Sporadic.Fi24I301Cover
