module

public import CFSG.RankThree.GF2n.Tim77.Sec3Conj
public import CFSG.RankThree.GF2n.Tim77.InvolAutDefs
public import CFSG.RankThree.GF2n.Tim77.InvolAut
public import CFSG.RankThree.GF2n.Tim77.InvolAutD
public import CFSG.RankThree.GF2n.Tim77Prop24
public import CFSG.RankThree.GF2n.Tim77Prop24TwoD
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.UnitaryTwoGen
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs
public import CFSG.RankThree.GF2n.Tim77.Sec3Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

@[expose] def Sec35Triv (X M : Subgroup G) (y : G) : Prop :=
  ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ M

theorem sec35_triv_mul {X M : Subgroup G} {y z : G} (hy : y ∈ normalizer (M : Set G))
    (hz : z ∈ normalizer (M : Set G)) (hyt : Sec35Triv X M y) (hzt : Sec35Triv X M z) :
    Sec35Triv X M (y * z) := by
  intro x hx
  have key : y * z * x * (y * z)⁻¹ * x⁻¹ =
      (y * (z * x * z⁻¹ * x⁻¹) * y⁻¹) * (y * x * y⁻¹ * x⁻¹) := by group
  rw [key]
  exact M.mul_mem ((Subgroup.mem_normalizer_iff.1 hy _).1 (hzt x hx)) (hyt x hx)

theorem sec35_triv_inv {X M : Subgroup G} {y : G} (hyX : y ∈ normalizer (X : Set G))
    (hyt : Sec35Triv X M y) : Sec35Triv X M y⁻¹ := by
  intro x hx
  have hx' : y⁻¹ * x * y ∈ X := by
    refine (Subgroup.mem_normalizer_iff.1 hyX _).2 ?_
    rw [show y * (y⁻¹ * x * y) * y⁻¹ = x by group]
    exact hx
  have h1 := hyt _ hx'
  rw [show y * (y⁻¹ * x * y) * y⁻¹ * (y⁻¹ * x * y)⁻¹ = x * (y⁻¹ * x⁻¹ * y) by group] at h1
  rw [show y⁻¹ * x * y⁻¹⁻¹ * x⁻¹ = (x * (y⁻¹ * x⁻¹ * y))⁻¹ by group]
  exact M.inv_mem h1

theorem sec35_triv_conj {X M : Subgroup G} {g c : G} (hgX : g ∈ normalizer (X : Set G))
    (hgM : g ∈ normalizer (M : Set G)) (hc : Sec35Triv X M c) :
    Sec35Triv X M (g * c * g⁻¹) := by
  intro x hx
  have hx' : g⁻¹ * x * g ∈ X := by
    refine (Subgroup.mem_normalizer_iff.1 hgX _).2 ?_
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    exact hx
  have h1 := (Subgroup.mem_normalizer_iff.1 hgM _).1 (hc _ hx')
  have e : g * (c * (g⁻¹ * x * g) * c⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ =
      g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹ * x⁻¹ := by
    group
  rw [e] at h1
  exact h1

theorem sec35_centralizes_conj {X M A₀ : Subgroup G}
    (hM : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ * m₂ = m₂ * m₁)
    (hXN : ∀ x ∈ X, x ∈ normalizer (M : Set G)) (hA₀M : A₀ ≤ M)
    {y : G} (hyt : Sec35Triv X M y) (hyA₀ : ∀ a ∈ A₀, y * a = a * y) {x : G} (hx : x ∈ X)
    {a' : G} (ha' : a' ∈ conjSubgroup x A₀) : y * a' = a' * y := by
  obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A₀, a' = x * a * x⁻¹ := by
    refine ⟨x⁻¹ * a' * x, ?_, by group⟩
    exact mem_conjSubgroup.mp ha'
  set m := y * x * y⁻¹ * x⁻¹ with hmdef
  have hm : m ∈ M := hyt x hx
  have hw : x * a * x⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 (hXN x hx) a).1 (hA₀M ha)
  have hya : y * a * y⁻¹ = a := mul_inv_eq_iff_eq_mul.2 (hyA₀ a ha)
  have e : y * (x * a * x⁻¹) * y⁻¹ = m * (x * a * x⁻¹) * m⁻¹ := by
    calc y * (x * a * x⁻¹) * y⁻¹ = (y * x * y⁻¹) * (y * a * y⁻¹) * (y * x⁻¹ * y⁻¹) := by group
      _ = (y * x * y⁻¹) * a * (y * x * y⁻¹)⁻¹ := by rw [hya]; group
      _ = m * (x * a * x⁻¹) * m⁻¹ := by rw [hmdef]; group
  have hcomm := hM m hm _ hw
  have h3 : m * (x * a * x⁻¹) * m⁻¹ = x * a * x⁻¹ := by
    rw [hcomm]
    group
  have h2 : y * (x * a * x⁻¹) * y⁻¹ = (x * a * x⁻¹) := by
    rw [e]
    exact h3
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem sec35_centralizes_M {X M A₀ B₁ : Subgroup G}
    (hM : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ * m₂ = m₂ * m₁)
    (hXN : ∀ x ∈ X, x ∈ normalizer (M : Set G)) (hA₀M : A₀ ≤ M) (hMsup : M = A₀ ⊔ B₁)
    (hgen : B₁ ≤ ⨆ x ∈ X, conjSubgroup x A₀)
    {y : G} (hyt : Sec35Triv X M y) (hyA₀ : ∀ a ∈ A₀, y * a = a * y) :
    ∀ m ∈ M, y * m = m * y := by
  have hle : M ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [hMsup]
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hyA₀ a ha
    · refine hgen.trans (iSup₂_le fun x hx => ?_)
      intro a' ha'
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact sec35_centralizes_conj hM hXN hA₀M hyt hyA₀ hx ha'
  intro m hm
  have := hle hm
  rw [Subgroup.mem_centralizer_iff] at this
  exact this y rfl

theorem sec35_comm_M_A [Finite G] {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M) {m a : G}
    (hm : m ∈ M) (ha : a ∈ A) : m * a * m⁻¹ * a⁻¹ ∈ L := by
  have hMN : M ≤ normalizer (A : Set G) := by
    rw [S.hM]
    exact sup_le (S.L_le.trans Subgroup.le_normalizer) (fun x hx => (S.mem_Lb.mp hx).2)
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hm
  have hc : a⁻¹ * lb * a * lb⁻¹ ∈ L := by
    have := S.commutator_mem_L (A.inv_mem ha) hlb
    rwa [inv_inv] at this
  have hla : l * a = a * l := S.comm_A (S.L_le hl) ha
  have hPA : (l * lb) * a * (l * lb)⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.1 (hMN hm) a).1 ha
  have hPeq : (l * lb) * a * (l * lb)⁻¹ = a * (l * (a⁻¹ * lb * a * lb⁻¹) * l⁻¹) := by
    calc (l * lb) * a * (l * lb)⁻¹ = (l * a) * a⁻¹ * lb * a * lb⁻¹ * l⁻¹ := by group
      _ = (a * l) * a⁻¹ * lb * a * lb⁻¹ * l⁻¹ := by rw [hla]
      _ = a * (l * (a⁻¹ * lb * a * lb⁻¹) * l⁻¹) := by group
  have hw : l * (a⁻¹ * lb * a * lb⁻¹) * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hc) (L.inv_mem hl)
  have hcomm : a * (l * (a⁻¹ * lb * a * lb⁻¹) * l⁻¹) = (l * (a⁻¹ * lb * a * lb⁻¹) * l⁻¹) * a :=
    S.comm_A ha (S.L_le hw)
  have e2 : l * lb * a * (l * lb)⁻¹ * a⁻¹ = l * (a⁻¹ * lb * a * lb⁻¹) * l⁻¹ := by
    rw [hPeq, hcomm]
    group
  rw [e2]
  exact hw

theorem sec35_le_of_normal_two [Finite G] {X M N : Subgroup G} [(M.subgroupOf X).Normal]
    (hO2 : ∀ K : Subgroup (↥X ⧸ M.subgroupOf X), K.Normal → IsPGroup 2 K → K = ⊥)
    (hNX : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hNle : N ≤ X) (hN2 : ∀ n ∈ N, n * n = 1) :
    N ≤ M := by
  have hNn : (N.subgroupOf X).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := hNX g.1 g.2 n hn
      simpa using this⟩
  have hKn : ((N.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  have hKp : IsPGroup 2 ((N.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) := by
    rintro ⟨g, hg⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    have hy2 : y * y = 1 := Subtype.ext (hN2 y.1 (Subgroup.mem_subgroupOf.mp hy))
    have hy1 : y ^ 2 = 1 := by rw [sq]; exact hy2
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hy1, map_one]
  intro n hn
  have hnX : n ∈ X := hNle hn
  have hmem : QuotientGroup.mk' (M.subgroupOf X) (⟨n, hnX⟩ : ↥X) ∈
      (N.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hn)
  rw [hO2 _ hKn hKp, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmem)

theorem sec35_normalizes_M
    [Finite G] {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M) {b : G}
    (hb : b ∈ normalizer ((A ⊔ Ab : Subgroup G) : Set G)) : b ∈ normalizer (M : Set G) := by
  obtain ⟨hN, hO2, -⟩ := S.exists_models CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  haveI := hN
  have hMX : A ⊔ Ab ≤ normalizer (M : Set G) := S.sup_le_normalizer_M
  have hMle : M ≤ A ⊔ Ab := by
    rw [S.hM]
    exact sup_le (S.L_le.trans le_sup_left) (S.Lb_le.trans le_sup_right)
  have key : ∀ c ∈ normalizer ((A ⊔ Ab : Subgroup G) : Set G), conjSubgroup c M ≤ M := by
    intro c hc
    apply sec35_le_of_normal_two (X := A ⊔ Ab) hO2
    · intro x hx n hn
      rw [mem_conjSubgroup] at hn ⊢
      have hy : c⁻¹ * x * c ∈ A ⊔ Ab := by
        refine (Subgroup.mem_normalizer_iff.1 hc _).2 ?_
        rw [show c * (c⁻¹ * x * c) * c⁻¹ = x by group]
        exact hx
      have e : c⁻¹ * (x * n * x⁻¹) * c = (c⁻¹ * x * c) * (c⁻¹ * n * c) * (c⁻¹ * x * c)⁻¹ := by
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hMX hy) _).1 hn
    · intro n hn
      rw [mem_conjSubgroup] at hn
      have := (Subgroup.mem_normalizer_iff.1 hc (c⁻¹ * n * c)).1 (hMle hn)
      rwa [show c * (c⁻¹ * n * c) * c⁻¹ = n by group] at this
    · intro n hn
      rw [mem_conjSubgroup] at hn
      have hmm : (c⁻¹ * n * c) * (c⁻¹ * n * c) = 1 := by
        rw [← sq]
        exact S.isElemAbelian_M.2 _ hn
      calc n * n = c * ((c⁻¹ * n * c) * (c⁻¹ * n * c)) * c⁻¹ := by group
        _ = 1 := by rw [hmm]; group
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · refine key b hb (mem_conjSubgroup.2 ?_)
    rw [show b⁻¹ * (b * h * b⁻¹) * b = h by group]
    exact hh
  · exact key b⁻¹ (inv_mem hb) (mem_conjSubgroup.2 (by rw [inv_inv]; exact hh))

theorem sec35_mem_normalizer_of_comm {a : G} {T : Subgroup G} (h : ∀ t ∈ T, a * t = t * a) :
    a ∈ normalizer (T : Set G) := by
  have h' : ∀ t ∈ T, a⁻¹ * t = t * a⁻¹ := fun t ht => by
    calc a⁻¹ * t = a⁻¹ * (t * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * t) * a⁻¹ := by rw [← h t ht]
      _ = t * a⁻¹ := by group
  refine Subgroup.mem_normalizer_iff.2 fun t => ⟨fun ht => ?_, fun ht => ?_⟩
  · have e : a * t * a⁻¹ = t := by rw [h t ht]; group
    rw [e]
    exact ht
  · have hs : a * t * a⁻¹ ∈ T := ht
    have e2 : a⁻¹ * (a * t * a⁻¹) * a = a * t * a⁻¹ := by
      rw [h' _ hs]
      group
    have e3 : t = a * t * a⁻¹ := by
      calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
        _ = a * t * a⁻¹ := e2
    rw [e3]
    exact hs

@[expose] def sec35BA (A B : Subgroup G) (hBC : ∀ b ∈ B, ∀ a ∈ A, a * b = b * a) :
    Subgroup G where
  carrier := {h | ∃ b ∈ B, ∃ a ∈ A, h = b * a}
  mul_mem' := by
    rintro _ _ ⟨b, hb, a, ha, rfl⟩ ⟨b', hb', a', ha', rfl⟩
    refine ⟨b * b', B.mul_mem hb hb', a * a', A.mul_mem ha ha', ?_⟩
    calc b * a * (b' * a') = b * (a * b') * a' := by group
      _ = b * (b' * a) * a' := by rw [hBC b' hb' a ha]
      _ = b * b' * (a * a') := by group
  one_mem' := ⟨1, B.one_mem, 1, A.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨b, hb, a, ha, rfl⟩
    refine ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, ?_⟩
    have h := congrArg (fun z : G => z⁻¹) (hBC b hb a ha)
    simp only [mul_inv_rev] at h
    rw [mul_inv_rev]
    exact h.symm

@[expose] def sec35C (X M H : Subgroup G)
    (hH : ∀ h ∈ H, h ∈ normalizer (X : Set G) ∧ h ∈ normalizer (M : Set G)) : Subgroup G where
  carrier := {h | h ∈ H ∧ Sec35Triv X M h}
  mul_mem' := by
    rintro _ _ ⟨h1, t1⟩ ⟨h2, t2⟩
    exact ⟨H.mul_mem h1 h2, sec35_triv_mul (hH _ h1).2 (hH _ h2).2 t1 t2⟩
  one_mem' := ⟨H.one_mem, fun x _ => by simpa using M.one_mem⟩
  inv_mem' := by
    rintro _ ⟨h1, t1⟩
    exact ⟨H.inv_mem h1, sec35_triv_inv (hH _ h1).1 t1⟩

theorem sec35_core [Finite G] {A Ab L Lb M B : Subgroup G} (S : Prop24Setup A Ab L Lb M)
    (hBconj : ∃ g : G, B = conjSubgroup g A) (hBne : B ≠ A)
    (hBC : ∀ b ∈ B, ∀ a ∈ A, a * b = b * a)
    (hBX : B ≤ normalizer ((A ⊔ Ab : Subgroup G) : Set G))
    (hBM : ∀ b ∈ B, b ∈ normalizer (M : Set G))
    (hstep1 : ∀ b ∈ B, ∃ a ∈ A, Sec35Triv (A ⊔ Ab) M (a * b))
    (hgen : Lb ≤ ⨆ x ∈ A ⊔ Ab, conjSubgroup x L)
    (hroot : IsRootTypeIn 2 (centralizer (B : Set G)) A) : False := by
  have hXN : ∀ x ∈ A ⊔ Ab, x ∈ normalizer (M : Set G) := fun x hx => S.sup_le_normalizer_M hx
  have hMc : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ * m₂ = m₂ * m₁ := fun _ h₁ _ h₂ => S.comm_M h₁ h₂
  have hLM : L ≤ M := S.L_le_M
  have hMsup : M = L ⊔ Lb := S.hM
  have hAX : A ≤ normalizer ((A ⊔ Ab : Subgroup G) : Set G) :=
    le_trans le_sup_left Subgroup.le_normalizer
  have hAM : A ≤ normalizer (M : Set G) := fun a ha => hXN a (Subgroup.mem_sup_left ha)
  have hBTI : IsTI B := by
    obtain ⟨g, hg⟩ := hBconj
    rw [hg]
    exact isTI_conjSubgroup S.ti g
  have hAB : A ⊓ B = ⊥ := by
    obtain ⟨g, hg⟩ := hBconj
    rw [hg]
    exact inf_conjSubgroup_eq_bot_of_isTI S.ti (fun h => hBne (hg.trans h))
  obtain ⟨b₀, hb₀B, hb₀1, hb₀t⟩ : ∃ b ∈ B, b ≠ 1 ∧ Sec35Triv (A ⊔ Ab) M b := by
    by_contra hno
    have hno' : ∀ b ∈ B, Sec35Triv (A ⊔ Ab) M b → b = 1 := fun b hb ht =>
      not_not.1 fun h1 => hno ⟨b, hb, h1, ht⟩
    have hH : ∀ h ∈ sec35BA A B hBC,
        h ∈ normalizer ((A ⊔ Ab : Subgroup G) : Set G) ∧ h ∈ normalizer (M : Set G) := by
      rintro h ⟨b, hb, a, ha, rfl⟩
      exact ⟨mul_mem (hBX hb) (hAX ha), mul_mem (hBM b hb) (hAM ha)⟩
    set H := sec35BA A B hBC with hHdef
    set C := sec35C (A ⊔ Ab) M H hH with hCdef
    have hC : ∀ h, h ∈ C ↔ h ∈ H ∧ Sec35Triv (A ⊔ Ab) M h := fun h => Iff.rfl
    have hCn : (C.subgroupOf H).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnH, hnt⟩ := (hC _).1 hn
      exact (hC _).2 ⟨H.mul_mem (H.mul_mem g.2 hnH) (H.inv_mem g.2),
        sec35_triv_conj (hH _ g.2).1 (hH _ g.2).2 hnt⟩
    haveI := hCn
    have hLC : L ≤ C := by
      intro l hl
      refine (hC l).2 ⟨⟨1, B.one_mem, l, S.L_le hl, by simp⟩, ?_⟩
      intro x hx
      have h1 : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
      rw [h1]
      exact M.mul_mem (hLM hl)
        ((Subgroup.mem_normalizer_iff.1 (hXN x hx) l⁻¹).1 (M.inv_mem (hLM hl)))
    have hAH : A ≤ H := fun a ha => ⟨1, B.one_mem, a, ha, by simp⟩
    have hBinj : Function.Injective (fun b : ↥B =>
        (QuotientGroup.mk (⟨(b : G), ⟨(b : G), b.2, 1, A.one_mem, (mul_one _).symm⟩⟩ : ↥H) :
          ↥H ⧸ C.subgroupOf H)) := by
      intro b b' hbb
      dsimp only at hbb
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hbb
      have h1 : (b : G)⁻¹ * (b' : G) ∈ C := by simpa using hbb
      obtain ⟨-, ht⟩ := (hC _).1 h1
      exact Subtype.ext (inv_mul_eq_one.1 (hno' _ (B.mul_mem (B.inv_mem b.2) b'.2) ht))
    have hcardB : Nat.card B ≤ Nat.card (↥H ⧸ C.subgroupOf H) :=
      Nat.card_le_card_of_injective _ hBinj
    let f : ↥A →* ↥H ⧸ C.subgroupOf H :=
      (QuotientGroup.mk' (C.subgroupOf H)).comp (Subgroup.inclusion hAH)
    have hfs : Function.Surjective f := by
      intro z
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨b, hb, a', ha', hh⟩ := h.2
      obtain ⟨a, ha, hta⟩ := hstep1 b hb
      have hab_H : a * b ∈ H := ⟨b, hb, a, ha, hBC b hb a ha⟩
      have hab : a * b ∈ C := (hC _).2 ⟨hab_H, hta⟩
      have hc1 : a' * (a * b) = a * b * a' := by
        rw [← mul_assoc, S.comm_A ha' ha, mul_assoc, hBC b hb a' ha', ← mul_assoc]
      have e : (a⁻¹ * a')⁻¹ * (h : G) = a * b := by
        rw [hh]
        calc (a⁻¹ * a')⁻¹ * (b * a') = a'⁻¹ * (a * b * a') := by group
          _ = a'⁻¹ * (a' * (a * b)) := by rw [hc1]
          _ = a * b := by group
      refine ⟨⟨a⁻¹ * a', A.mul_mem (A.inv_mem ha) ha'⟩, ?_⟩
      show QuotientGroup.mk (⟨a⁻¹ * a', hAH (A.mul_mem (A.inv_mem ha) ha')⟩ : ↥H) =
        QuotientGroup.mk h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have key : ((⟨a⁻¹ * a', hAH (A.mul_mem (A.inv_mem ha) ha')⟩ : ↥H))⁻¹ * h =
          (⟨a * b, hab_H⟩ : ↥H) := Subtype.ext e
      rw [key]
      exact hab
    have hker : L.subgroupOf A ≤ f.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' (C.subgroupOf H) (Subgroup.inclusion hAH x) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hLC (Subgroup.mem_subgroupOf.1 hx)
    have hquot : Nat.card (↥H ⧸ C.subgroupOf H) = f.ker.index := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfs).toEquiv]
      rfl
    have hidx : f.ker.index ≤ (L.subgroupOf A).index := Subgroup.index_antitone hker
    obtain ⟨g', hg'⟩ := hBconj
    have hBA : Nat.card B = Nat.card A := by
      rw [hg']
      exact card_conjSubgroup g' A
    have hAk : Nat.card A = (L.subgroupOf A).index * Nat.card L := by
      rw [← Subgroup.card_mul_index (L.subgroupOf A), mul_comm]
      congr 1
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.L_le).toEquiv
    have hL1 : 1 < Nat.card L := (Subgroup.one_lt_card_iff_ne_bot L).2 S.ne_bot
    have hpos : 0 < (L.subgroupOf A).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h1 : Nat.card B ≤ (L.subgroupOf A).index := hcardB.trans (hquot.le.trans hidx)
    nlinarith
  have hcent : ∀ m ∈ M, b₀ * m = m * b₀ :=
    sec35_centralizes_M hMc hXN hLM hMsup hgen hb₀t (fun a ha => (hBC b₀ hb₀B a (S.L_le ha)).symm)
  have hMN : ∀ m ∈ M, m ∈ normalizer (B : Set G) := fun m hm =>
    mem_normalizer_of_commute_of_isTI hBTI hb₀B hb₀1 (hcent m hm).symm
  have hMB : ∀ m ∈ M, ∀ b ∈ B, m * b = b * m := by
    intro m hm b hb
    obtain ⟨a, ha, hta⟩ := hstep1 b hb
    have hcL : ∀ l ∈ L, (a * b) * l = l * (a * b) := by
      intro l hl
      calc a * b * l = a * (b * l) := by group
        _ = a * (l * b) := by rw [← hBC b hb l (S.L_le hl)]
        _ = (a * l) * b := by group
        _ = (l * a) * b := by rw [S.comm_A ha (S.L_le hl)]
        _ = l * (a * b) := by group
    have hcM : ∀ m' ∈ M, (a * b) * m' = m' * (a * b) :=
      sec35_centralizes_M hMc hXN hLM hMsup hgen hta hcL
    have hcMinv : (a * b) * m⁻¹ * (a * b)⁻¹ = m⁻¹ :=
      mul_inv_eq_iff_eq_mul.2 (hcM m⁻¹ (M.inv_mem hm))
    have hA_mem : m * b * m⁻¹ * b⁻¹ ∈ A := by
      have e : m * b * m⁻¹ * b⁻¹ = m * a⁻¹ * m⁻¹ * a := by
        calc m * b * m⁻¹ * b⁻¹ = m * a⁻¹ * ((a * b) * m⁻¹ * (a * b)⁻¹) * a := by group
          _ = m * a⁻¹ * m⁻¹ * a := by rw [hcMinv]
      rw [e]
      have := sec35_comm_M_A S hm (A.inv_mem ha)
      rw [inv_inv] at this
      exact S.L_le this
    have hB_mem : m * b * m⁻¹ * b⁻¹ ∈ B := by
      have h1 : m * b * m⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (hMN m hm) b).1 hb
      exact B.mul_mem h1 (B.inv_mem hb)
    have h0 : m * b * m⁻¹ * b⁻¹ ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨hA_mem, hB_mem⟩
    rw [hAB, Subgroup.mem_bot] at h0
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h0)
  have hBAb : ∀ b ∈ B, b ∈ normalizer (Ab : Set G) := by
    intro b hb
    obtain ⟨⟨x, hxLb⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 S.Lb_ne_bot
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact mem_normalizer_of_commute_of_isTI S.ti_Ab (S.Lb_le hxLb) hx1'
      (hMB x (S.Lb_le_M hxLb) b hb).symm
  obtain ⟨g0, hg0⟩ := S.conj
  obtain ⟨g', hg'⟩ := hBconj
  have hBAbconj : B = conjSubgroup (g' * g0⁻¹) Ab := by
    rw [hg0, conjSubgroup_mul, ← conjSubgroup_mul g0⁻¹ g0 A, inv_mul_cancel, conjSubgroup_one]
    exact hg'
  have hgle : conjSubgroup (g' * g0⁻¹) Ab ≤ normalizer (Ab : Set G) := by
    rw [← hBAbconj]
    exact hBAb
  have hel := tim77_2_3 S.elem_Ab S.ti_Ab hgle
  rw [← hBAbconj] at hel
  have hcomm : ∀ b ∈ B, ∀ x ∈ Ab, b * x = x * b := by
    intro b hb x hx
    exact (congrArg Subtype.val (hel.1.is_comm.comm ⟨x, Subgroup.mem_sup_left hx⟩
      ⟨b, Subgroup.mem_sup_right hb⟩)).symm
  have hAC : A ≤ centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hBC b hb a ha).symm
  have hAbC : Ab ≤ centralizer (B : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hcomm b hb x hx
  have hXC : A ⊔ Ab ≤ centralizer (B : Set G) := sup_le hAC hAbC
  obtain ⟨x0, hx0X, hx0⟩ := S.exists_conj_eq
  have hnz : normalizerIn A (conjSubgroup x0 A) ≠ ⊥ := by
    rw [← hx0]
    show A ⊓ normalizer (Ab : Set G) ≠ ⊥
    rw [← S.hL]
    exact S.ne_bot
  obtain ⟨-, -, -, hnorm⟩ := hroot
  have hcomm' : ∀ a ∈ A, ∀ b ∈ Ab, a * b = b * a := fun a ha b hb =>
    hnorm x0 (hXC hx0X) hnz a ha b (hx0 ▸ hb)
  have hAN : A ≤ normalizer (Ab : Set G) := fun a ha =>
    sec35_mem_normalizer_of_comm (fun t ht => hcomm' a ha t ht)
  apply S.ne
  rw [S.hL]
  exact inf_eq_left.2 hAN

theorem sec35_exists_fixed [Finite G] {W : Subgroup G} (hW : W ≠ ⊥)
    (hWc : ∀ w₁ ∈ W, ∀ w₂ ∈ W, w₁ * w₂ = w₂ * w₁) (hWel : ∀ w ∈ W, w * w = 1)
    {t : G} (htW : t ∈ normalizer (W : Set G)) (ht2 : t * t = 1) :
    ∃ w ∈ W, w ≠ 1 ∧ t * w = w * t := by
  by_contra hno
  push_neg at hno
  have hτW : ∀ w ∈ W, t * w * t⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.1 htW w).1 hw
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hτinv : ∀ w : G, t * (t * w * t⁻¹) * t⁻¹ = w := fun w => by
    rw [ht']
    calc t * (t * w * t) * t = (t * t) * w * (t * t) := by group
      _ = w := by rw [ht2]; group
  let φ : ↥W → ↥W := fun u => ⟨u * (t * u * t⁻¹), W.mul_mem u.2 (hτW u u.2)⟩
  have hφinj : Function.Injective φ := by
    intro u v huv
    have h : (u : G) * (t * u * t⁻¹) = v * (t * v * t⁻¹) := congrArg Subtype.val huv
    have hu' : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_right (hWel u u.2)
    have hv' : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right (hWel v v.2)
    have hτu : t * u * t⁻¹ = (u : G)⁻¹ * (v * (t * v * t⁻¹)) := by
      rw [← h]
      group
    have hfix : t * ((u : G) * (v : G)⁻¹) * t⁻¹ = (u : G) * (v : G)⁻¹ := by
      calc t * ((u : G) * (v : G)⁻¹) * t⁻¹ = (t * u * t⁻¹) * (t * v * t⁻¹)⁻¹ := by group
        _ = (u : G)⁻¹ * (v * (t * v * t⁻¹)) * (t * v * t⁻¹)⁻¹ := by rw [hτu]
        _ = (u : G)⁻¹ * v := by group
        _ = (u : G) * (v : G)⁻¹ := by rw [hu', hv']
    have hw1 : (u : G) * (v : G)⁻¹ = 1 := by
      by_contra hw1
      exact hno _ (W.mul_mem u.2 (W.inv_mem v.2)) hw1 (mul_inv_eq_iff_eq_mul.1 hfix)
    exact Subtype.ext (mul_inv_eq_one.1 hw1)
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.1 hφinj
  have hfixall : ∀ w ∈ W, t * w * t⁻¹ = w := by
    intro w hw
    obtain ⟨u, hu⟩ := hφsurj ⟨w, hw⟩
    have hu' : (u : G) * (t * u * t⁻¹) = w := congrArg Subtype.val hu
    rw [← hu']
    calc t * (u * (t * u * t⁻¹)) * t⁻¹ = (t * u * t⁻¹) * (t * (t * u * t⁻¹) * t⁻¹) := by group
      _ = (t * u * t⁻¹) * u := by rw [hτinv u]
      _ = u * (t * u * t⁻¹) := hWc _ (hτW u u.2) _ u.2
  apply hW
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  exact hno w hw hw1 (mul_inv_eq_iff_eq_mul.1 (hfixall w hw))

theorem sec35_gen_dihedral [Finite G] {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
    (hAL : L.relIndex A = 2) : Lb ≤ ⨆ x ∈ A ⊔ Ab, conjSubgroup x L := by
  obtain ⟨s, -, hsM, hs⟩ := S.tim77_2_4_two_dihedral hAL
  set N : Subgroup G := ⨆ x ∈ A ⊔ Ab, conjSubgroup x L with hNdef
  have hLN : L ≤ N := by
    have := le_iSup₂ (f := fun x (_ : x ∈ A ⊔ Ab) => conjSubgroup x L) 1 (A ⊔ Ab).one_mem
    rwa [conjSubgroup_one] at this
  have hNconj : ∀ y ∈ A ⊔ Ab, N ≤ conjSubgroup y N := by
    intro y hy
    refine iSup₂_le fun x hx => ?_
    have e : conjSubgroup x L = conjSubgroup y (conjSubgroup (y⁻¹ * x) L) := by
      rw [← conjSubgroup_mul, mul_inv_cancel_left]
    rw [e]
    refine (conjSubgroup_le_conj_iff y).2 ?_
    exact le_iSup₂ (f := fun x (_ : x ∈ A ⊔ Ab) => conjSubgroup x L) (y⁻¹ * x)
      ((A ⊔ Ab).mul_mem ((A ⊔ Ab).inv_mem hy) hx)
  have hNX : ∀ y ∈ A ⊔ Ab, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    have := hNconj y⁻¹ ((A ⊔ Ab).inv_mem hy) hn
    rw [mem_conjSubgroup, inv_inv] at this
    exact this
  have hTX : ∀ W ∈ s, W ≤ N := by
    intro W hW
    obtain ⟨hWM, hXW, hW1, hirr⟩ := hs W hW
    obtain ⟨t, htA, htL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
    have htW : t ∈ normalizer (W : Set G) := hXW (Subgroup.mem_sup_left htA)
    obtain ⟨w, hwW, hw1, htw⟩ := sec35_exists_fixed hW1
      (fun w₁ h₁ w₂ h₂ => S.comm_M (hWM h₁) (hWM h₂))
      (fun w hw => by rw [← sq]; exact S.isElemAbelian_M.2 w (hWM hw)) htW (S.sq_A htA)
    have hwL : w ∈ L := S.mem_L_of_commute_M htA htL (hWM hwW) htw
    have fwd : ∀ y ∈ A ⊔ Ab, ∀ h ∈ N ⊓ W, y * h * y⁻¹ ∈ N ⊓ W := fun y hy h hh =>
      ⟨hNX y hy h hh.1, (Subgroup.mem_normalizer_iff.1 (hXW hy) h).1 hh.2⟩
    have hU : A ⊔ Ab ≤ normalizer ((N ⊓ W : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => fwd y hy h hh, fun hh => ?_⟩
      have := fwd y⁻¹ ((A ⊔ Ab).inv_mem hy) _ hh
      rwa [show y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h by group] at this
    rcases hirr (N ⊓ W) inf_le_right hU with hbot | heq
    · exfalso
      have hwU : w ∈ N ⊓ W := ⟨hLN hwL, hwW⟩
      rw [hbot, Subgroup.mem_bot] at hwU
      exact hw1 hwU
    · calc W = N ⊓ W := heq.symm
        _ ≤ N := inf_le_left
  have hMN : M ≤ N := by
    rw [← hsM]
    exact Finset.sup_le fun W hW => hTX W hW
  exact S.Lb_le_M.trans hMN

theorem sec35_root_transport [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) :
    IsRootTypeIn 2 (centralizer (B : Set G)) A := by
  obtain ⟨g', hg'⟩ := h.nota.conj
  have hAC_B : A ≤ centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb =>
      ((Subgroup.mem_centralizer_iff.1 (h.nota.le hb).2) a ha).symm
  have hBA : conjSubgroup g'⁻¹ B = A := by
    rw [hg', ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hAC : conjSubgroup g'⁻¹ A ≤ centralizer (A : Set G) := by
    have e1 : centralizer (A : Set G) = conjSubgroup g'⁻¹ (centralizer (B : Set G)) := by
      rw [← hBA, centralizer_conjSubgroup_eq]
    rw [e1]
    exact (conjSubgroup_le_conj_iff g'⁻¹).2 hAC_B
  have h1 := h.hyp.rootTypeInCentralizer g'⁻¹ hAC
  have h2 := (isRootTypeIn_conjSubgroup_iff_t77 (p := 2) g').2 h1
  have e2 : conjSubgroup g' (conjSubgroup g'⁻¹ A) = A := by
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have e3 : conjSubgroup g' (centralizer (A : Set G)) = centralizer (B : Set G) := by
    rw [← centralizer_conjSubgroup_eq, ← hg']
  rw [e2, e3] at h2
  exact h2

theorem sec35_step1_of_inner (hInner : Prop24InnerStatement) [Finite G]
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hr : 2 < (Section3.A0 A Abar).relIndex A) {b : G} (hb : b ∈ B)
    (hBX : b ∈ normalizer ((A ⊔ Abar : Subgroup G) : Set G)) :
    ∃ a ∈ A, Sec35Triv (A ⊔ Abar) (Section3.M A Abar) (a * b) := by
  obtain ⟨g, hg⟩ := h.nota.conj
  have hbb : b * b = 1 := by
    rw [← sq]
    exact (isElemAbelian_conj h.hyp.elemAbelian g).2 b (hg ▸ hb)
  obtain ⟨a, ha, hy⟩ := hInner G A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar)
    (Section3.M A Abar) h.setup hr b (conjSubgroup_eq_self_iff.2 hBX)
    (Subgroup.mem_centralizer_iff.2 fun c hc => (Subgroup.mem_centralizer_iff.1
      (h.nota.le hb).2) c hc) (fun x _ => by rw [hbb]; simpa using (Section3.M A Abar).one_mem)
  refine ⟨a, ha, ?_⟩
  have hyN : a * b ∈ normalizer ((A ⊔ Abar : Subgroup G) : Set G) :=
    mul_mem ((le_trans le_sup_left Subgroup.le_normalizer) ha) hBX
  have ht : Sec35Triv (A ⊔ Abar) (Section3.M A Abar) (a * b)⁻¹ := by
    intro x hx
    have := hy x⁻¹ (inv_mem hx)
    rw [inv_inv] at this
    show (a * b)⁻¹ * x * (a * b)⁻¹⁻¹ * x⁻¹ ∈ _
    rw [inv_inv]
    exact this
  have ht2 := sec35_triv_inv (inv_mem hyN) ht
  rw [inv_inv] at ht2
  exact ht2

@[expose] def Sec35DihedralStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    (Section3.A0 A Abar).relIndex A = 2 → ∀ b ∈ B,
      b ∈ normalizer ((A ⊔ Abar : Subgroup G) : Set G) →
      ∃ a ∈ A, Sec35Triv (A ⊔ Abar) (Section3.M A Abar) (a * b)

@[expose] def Sec35GenLSStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    2 < (Section3.A0 A Abar).relIndex A →
      Section3.Abar0 A Abar ≤ ⨆ x ∈ A ⊔ Abar, conjSubgroup x (Section3.A0 A Abar)

theorem sec35_of_dihedral
    (hInner : Prop24InnerStatement) (hD : Sec35DihedralStatement)
    (hgenLS : Sec35GenLSStatement) : Tim77Sec35Statement := by
  intro G _ _ A Abar S₀ B h hB
  have hBX : B ≤ normalizer ((A ⊔ Abar : Subgroup G) : Set G) := hB
  have hBM : ∀ b ∈ B, b ∈ normalizer (Section3.M A Abar : Set G) := fun b hb =>
    sec35_normalizes_M h.setup (hBX hb)
  have hBC : ∀ b ∈ B, ∀ a ∈ A, a * b = b * a := fun b hb a ha =>
    (Subgroup.mem_centralizer_iff.1 (h.nota.le hb).2) a ha
  have hr_ne0 : (Section3.A0 A Abar).relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hr_ne1 : (Section3.A0 A Abar).relIndex A ≠ 1 := by
    intro h1
    apply h.a0_ne
    have hle : A ≤ Section3.A0 A Abar := Subgroup.relIndex_eq_one.1 h1
    exact le_antisymm (by rw [h.a0_eq]; exact inf_le_left) hle
  have hgen : Section3.Abar0 A Abar ≤ ⨆ x ∈ A ⊔ Abar, conjSubgroup x (Section3.A0 A Abar) := by
    rcases (show 2 < (Section3.A0 A Abar).relIndex A ∨ (Section3.A0 A Abar).relIndex A = 2 by
      omega) with hr | hr
    · exact hgenLS G A Abar S₀ B h hr
    · exact sec35_gen_dihedral h.setup hr
  have hstep1 : ∀ b ∈ B, ∃ a ∈ A, Sec35Triv (A ⊔ Abar) (Section3.M A Abar) (a * b) := by
    intro b hb
    rcases (show 2 < (Section3.A0 A Abar).relIndex A ∨ (Section3.A0 A Abar).relIndex A = 2 by
      omega) with hr | hr
    · exact sec35_step1_of_inner hInner h hr hb (hBX hb)
    · exact hD G A Abar S₀ B h hr b hb (hBX hb)
  exact sec35_core h.setup h.nota.conj h.nota.ne hBC hBX hBM hstep1 hgen
    (sec35_root_transport h)

theorem sec35Dihedral_holds :
    Sec35DihedralStatement := by
  intro G _ _ A Abar S₀ B h hr b hb hBX
  obtain ⟨a, ha, hy⟩ := prop24InnerD_holds G A Abar (Section3.A0 A Abar)
    (Section3.Abar0 A Abar) (Section3.M A Abar) h.setup hr b (conjSubgroup_eq_self_iff.2 hBX)
    (Subgroup.mem_centralizer_iff.2 fun c hc => (Subgroup.mem_centralizer_iff.1
      (h.nota.le hb).2) c hc)
  refine ⟨a, ha, ?_⟩
  have hyN : a * b ∈ normalizer ((A ⊔ Abar : Subgroup G) : Set G) :=
    mul_mem ((le_trans le_sup_left Subgroup.le_normalizer) ha) hBX
  have ht : Sec35Triv (A ⊔ Abar) (Section3.M A Abar) (a * b)⁻¹ := by
    intro x hx
    have := hy x⁻¹ (inv_mem hx)
    rw [inv_inv] at this
    show (a * b)⁻¹ * x * (a * b)⁻¹⁻¹ * x⁻¹ ∈ _
    rw [inv_inv]
    exact this
  have ht2 := sec35_triv_inv (inv_mem hyN) ht
  rw [inv_inv] at ht2
  exact ht2

theorem sec35GenLS_holds : Sec35GenLSStatement := by
  intro G _ _ A Abar S₀ B h _
  obtain ⟨k, hk, hLb⟩ := sec34_exists_k h.setup
  rw [hLb]
  exact le_iSup₂ (f := fun x (_ : x ∈ A ⊔ Abar) => conjSubgroup x (Section3.A0 A Abar)) k hk

theorem tim77Sec35_holds :
    Tim77Sec35Statement :=
  sec35_of_dihedral prop24Inner_holds sec35Dihedral_holds sec35GenLS_holds

end CFSG.RankThree.GF2n.Tim77
