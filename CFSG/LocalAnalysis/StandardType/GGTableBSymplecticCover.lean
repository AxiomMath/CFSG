module

public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift
import CFSG.RankThree.PartOne.S15K.CentralCover
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

section General

variable {G : Type*} [Group G]

theorem isSubnormal_trans_normal {A B C : Subgroup G} (hAB : IsSubnormal A B) (hBC : B ≤ C)
    (hn : (B.subgroupOf C).Normal) : IsSubnormal A C :=
  hAB.trans (.step hBC hn (.refl C))

theorem map_conj_eq_self {X : Subgroup G} {x : G} (hx : x ∈ X) :
    X.map (MulAut.conj x).toMonoidHom = X := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact X.mul_mem (X.mul_mem hx hz) (X.inv_mem hx)
  · intro hy
    refine ⟨x⁻¹ * y * x, X.mul_mem (X.mul_mem (X.inv_mem hx) hy) hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem largeEvenLayer_conj_mem {X : Subgroup G} {x : G} (hx : x ∈ X) {k : G}
    (hk : k ∈ LargeEvenLayer X) : x * k * x⁻¹ ∈ LargeEvenLayer X := by
  have hle : (LargeEvenLayer X).map (MulAut.conj x).toMonoidHom ≤ LargeEvenLayer X := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h := isComponentOf_map_of_injective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective hK
    rw [map_conj_eq_self hx] at h
    exact le_sSup h
  exact hle ⟨k, hk, rfl⟩

theorem commute_of_mem_commutator {Y : Subgroup G} {x : G}
    (h : ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center G) {k : G} (hk : k ∈ ⁅Y, Y⁆) :
    x * k = k * x := by
  have hle : ⁅Y, Y⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
    have e₁ : x * y₁ * x⁻¹ = (x * y₁ * x⁻¹ * y₁⁻¹) * y₁ := by group
    have e₂ : x * y₂ * x⁻¹ = (x * y₂ * x⁻¹ * y₂⁻¹) * y₂ := by group
    have key : x * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * x⁻¹ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by
      calc x * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * x⁻¹ = (x * y₁ * x⁻¹) * (x * y₂ * x⁻¹) *
            (x * y₁ * x⁻¹)⁻¹ * (x * y₂ * x⁻¹)⁻¹ := by group
        _ = ((x * y₁ * x⁻¹ * y₁⁻¹) * y₁) * ((x * y₂ * x⁻¹ * y₂⁻¹) * y₂) *
            ((x * y₁ * x⁻¹ * y₁⁻¹) * y₁)⁻¹ * ((x * y₂ * x⁻¹ * y₂⁻¹) * y₂)⁻¹ := by rw [← e₁, ← e₂]
        _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := commutator_mul_central (h y₁ hy₁) (h y₂ hy₂)
    calc (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * x = x * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * x⁻¹ * x := by rw [key]
      _ = x * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by group
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm

end General

end TableBSymp

@[expose] def GGEndNodeElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    ∃ t ∈ A, t ≠ 1 ∧
      IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set R)))
        (Subgroup.centralizer ({t} : Set R)) ∧
      ∀ s ∈ A, ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set R)), s * j = j * s) ↔
        s ∈ Subgroup.zpowers t)

namespace TableBSymp

section Cover

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

theorem eq_conj_of_induces (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (a : MulAut L') (t : L') (h : ∀ l, ψ (a l) = ψ t * ψ l * (ψ t)⁻¹) (l : L') :
    a l = t * l * t⁻¹ := by
  have hP : Group.IsPerfect L' := ⟨hperf⟩
  have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ hker hP a.toMonoidHom
    (MulAut.conj t).toMonoidHom (fun u => by
      show ψ (a u) = ψ (t * u * t⁻¹)
      rw [h u, map_mul, map_mul, map_inv])
  exact key l

theorem isQuasisimple_iff (X : Type*) [Group X] :
    Assembly.IsQuasisimple X ↔ CFSG.IsQuasisimple X :=
  CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X

theorem layer_centralizer_lift (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {t' : L'}
    (hcomp : IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({ψ t'} : Set R)))
      (Subgroup.centralizer ({ψ t'} : Set R))) :
    LargeEvenLayer (Subgroup.centralizer ({t'} : Set L')) =
        ⁅(LargeEvenLayer (Subgroup.centralizer ({ψ t'} : Set R))).comap ψ,
          (LargeEvenLayer (Subgroup.centralizer ({ψ t'} : Set R))).comap ψ⁆ ∧
      IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t'} : Set L')))
        (Subgroup.centralizer ({t'} : Set L')) := by
  set Ct := Subgroup.centralizer ({ψ t'} : Set R) with hCt
  set Kb := LargeEvenLayer Ct with hKb
  set C := Subgroup.centralizer ({t'} : Set L') with hC
  set Y := Kb.comap ψ with hY
  set K := ⁅Y, Y⁆ with hK
  have hKbq : CFSG.IsQuasisimple Kb := (isQuasisimple_iff _).mp hcomp.2.2
  have hKbperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.1 hKbq.1
  have hKq : CFSG.IsQuasisimple K :=
    CFSG.RankThree.PartOne.S15K.isQuasisimple_commutator_comap hψ hker hKbq
  have hYK : K ≤ Y := Subgroup.commutator_le_self Y
  have hKC : K ≤ C := by
    intro k hk
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    refine (commute_of_mem_commutator (x := t') (fun y hy => hker ?_) hk).symm
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hcomp.1 hy)
    rw [← h1]
    group
  have hCY : ∀ c ∈ C, ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := by
    intro c hc y hy
    show ψ (c * y * c⁻¹) ∈ Kb
    rw [map_mul, map_mul, map_inv]
    refine largeEvenLayer_conj_mem ?_ hy
    rw [hCt, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff.mp hc)]
  have hCK : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    have hle : K.map (MulAut.conj c).toMonoidHom ≤ K := by
      rw [hK, Subgroup.map_commutator]
      have hYc : Y.map (MulAut.conj c).toMonoidHom ≤ Y := by
        rintro _ ⟨y, hy, rfl⟩
        exact hCY c hc y hy
      exact Subgroup.commutator_mono hYc hYc
    exact hle ⟨k, hk, rfl⟩
  have hKcomp : IsComponentOf K C := by
    refine ⟨hKC, IsSubnormal.step hKC ?_ (IsSubnormal.refl C), (isQuasisimple_iff _).mpr hKq⟩
    rw [Subgroup.normal_subgroupOf_iff hKC]
    intro k c hk hc
    exact hCK c hc k hk
  set Chat := Ct.comap ψ with hChat
  have hCChat : C ≤ Chat := by
    intro c hc
    show ψ c ∈ Ct
    rw [hCt, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff.mp hc)]
  have hCn : (C.subgroupOf Chat).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCChat]
    intro c g hc hg
    have hg' : ψ g * ψ t' = ψ t' * ψ g := Subgroup.mem_centralizer_singleton_iff.mp hg
    set z := g * t' * g⁻¹ * t'⁻¹ with hz
    have hzZ : z ∈ Subgroup.center L' := hker (by
      rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, hg']
      group)
    have hgt : g * t' * g⁻¹ = z * t' := by rw [hz]; group
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have hc' : (g * c * g⁻¹) * (g * t' * g⁻¹) = (g * t' * g⁻¹) * (g * c * g⁻¹) := by
      calc (g * c * g⁻¹) * (g * t' * g⁻¹) = g * (c * t') * g⁻¹ := by group
        _ = g * (t' * c) * g⁻¹ := by rw [hc]
        _ = (g * t' * g⁻¹) * (g * c * g⁻¹) := by group
    rw [hgt] at hc'
    have e := Subgroup.mem_center_iff.mp hzZ (g * c * g⁻¹)
    calc g * c * g⁻¹ * t' = z⁻¹ * ((g * c * g⁻¹) * (z * t')) := by
          rw [← mul_assoc (g * c * g⁻¹) z t', e]; group
      _ = z⁻¹ * ((z * t') * (g * c * g⁻¹)) := by rw [hc']
      _ = t' * (g * c * g⁻¹) := by group
  have hle_all : ∀ K' : Subgroup L', IsComponentOf K' C → K' ≤ K := by
    intro K' hK'
    have hK'q : CFSG.IsQuasisimple K' := (isQuasisimple_iff _).mp hK'.2.2
    have hsub : IsSubnormal K' Chat := isSubnormal_trans_normal hK'.2.1 hCChat hCn
    have hsubR : IsSubnormal (K'.map ψ) Ct := by
      have := isSubnormal_map_hom ψ hsub
      rwa [hChat, Subgroup.map_comap_eq_self_of_surjective hψ] at this
    have hrange : (ψ.comp K'.subtype).range = K'.map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hqR : CFSG.IsQuasisimple (K'.map ψ) := by
      have h := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_range hK'q (ψ.comp K'.subtype)
        (by
          intro x hx
          rw [Subgroup.mem_center_iff]
          intro y
          exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hx) y))
      rw [hrange] at h
      exact h
    have hcompR : IsComponentOf (K'.map ψ) Ct := by
      refine ⟨?_, hsubR, (isQuasisimple_iff _).mpr hqR⟩
      rintro _ ⟨k, hk, rfl⟩
      show ψ k ∈ Ct
      exact hCChat (hK'.1 hk)
    have hK'Y : K' ≤ Y := by
      rw [hY, ← Subgroup.map_le_iff_le_comap]
      exact le_sSup hcompR
    have hK'perf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.1 hK'q.1
    rw [← hK'perf]
    exact Subgroup.commutator_mono hK'Y hK'Y
  have hlayer : LargeEvenLayer C = K :=
    le_antisymm (sSup_le fun K' hK' => hle_all K' hK') (le_sSup hKcomp)
  exact ⟨hlayer, hlayer ▸ hKcomp⟩

end Cover

end TableBSymp

open TableBSymp in
theorem ggEndNode_of_elt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGEndNodeElt p r R) : GGEndNode p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  have hex : ∀ a : A, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    obtain ⟨t, rfl⟩ := hI hφI
    exact ⟨t, fun l => (hφ l).symm⟩
  have huniq : ∀ (a : MulAut L') (t t' : R), (∀ l, ψ (a l) = t * ψ l * t⁻¹) →
      (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e]
        _ = (t'⁻¹ * t) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hinner : ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a t' ht' => eq_conj_of_induces hker hperf (a : MulAut L') t' (fun l => by rw [hχ, ht'])
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hinner a 1 (by rw [map_one]; exact ha.symm)
    apply Subtype.ext
    ext l
    rw [h1 l]
    simp
  set Ab := χ.range with hAb
  have hAbA : IsElemAbelian p Ab := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcardAb : Nat.card Ab = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  obtain ⟨_, ⟨a₀, rfl⟩, ht1, hcomp, hcent⟩ := h Ab hAbA (hcardAb ▸ hr) (hcardAb ▸ h3)
  obtain ⟨t', ht'⟩ := hψ (χ a₀)
  have ha₀ := hinner a₀ t' ht'
  have hfix : ggFix (a₀ : MulAut L') = Subgroup.centralizer ({t'} : Set L') := by
    ext l
    rw [mem_ggFix, ha₀, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hl
      calc l * t' = t' * l * t'⁻¹ * t' := by rw [hl]
        _ = t' * l := by group
    · intro hl
      rw [← hl]
      group
  rw [← ht'] at hcomp hcent
  obtain ⟨hlayer, hcompL⟩ := layer_centralizer_lift hψ hker hcomp
  refine ⟨a₀, a₀.2, fun h1 => ht1 ?_, ?_, fun a' ha' => ?_⟩
  · have : a₀ = 1 := Subtype.ext h1
    rw [this, map_one]
  · rw [hfix]
    exact hcompL
  ·
    obtain ⟨s', hs'⟩ := hψ (χ ⟨a', ha'⟩)
    have hinn' := hinner ⟨a', ha'⟩ s' hs'
    set Kb := LargeEvenLayer (Subgroup.centralizer ({ψ t'} : Set R)) with hKb
    have hKbq : CFSG.IsQuasisimple Kb := (isQuasisimple_iff _).mp hcomp.2.2
    have hKbperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.1 hKbq.1
    have hmapK := CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hKbperf
    have hcent' := hcent (χ ⟨a', ha'⟩) ⟨⟨a', ha'⟩, rfl⟩
    rw [hfix, hlayer]
    constructor
    · intro hj
      have h1 : ∀ j ∈ Kb, χ ⟨a', ha'⟩ * j = j * χ ⟨a', ha'⟩ := by
        intro j hj'
        rw [← hmapK] at hj'
        obtain ⟨k, hk, rfl⟩ := hj'
        have e := hj k hk
        rw [hinn'] at e
        rw [← hs', ← map_mul, ← map_mul]
        congr 1
        calc s' * k = s' * k * s'⁻¹ * s' := by group
          _ = k * s' := by rw [e]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcent'.mp h1)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h2 : a₀ ^ n = ⟨a', ha'⟩ := hχinj (by rw [map_zpow, ← ht', hn])
      exact congrArg Subtype.val h2
    · intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h2 : a₀ ^ n = ⟨a', ha'⟩ := Subtype.ext hn
      have h3 : χ ⟨a', ha'⟩ ∈ Subgroup.zpowers (ψ t') :=
        Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [ht', ← map_zpow, h2]⟩
      have h4 := hcent'.mpr h3
      intro j hj
      rw [hinn']
      have hcomm := commute_of_mem_commutator (x := s')
        (Y := Kb.comap ψ) (fun y hy => hker (by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs', h4 (ψ y) hy]
          group)) hj
      rw [hcomm]
      group

namespace TableBSymp

end TableBSymp

end CFSG.StandardType
