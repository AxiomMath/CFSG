module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Choice
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Module
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Index
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_sup_of_commute' {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

omit [Finite G] in
theorem omegaOneCenter_le_inf_centralizer (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

omit [Finite G] in
theorem mem_normalizer_of_conj_le {K : Subgroup G} {g : G}
    (h1 : ∀ w ∈ K, g * w * g⁻¹ ∈ K) (h2 : ∀ w ∈ K, g⁻¹ * w * g⁻¹⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h1 w, fun hw => ?_⟩
  have := h2 _ hw
  simpa [mul_assoc] using this

omit [Finite G] in
theorem conj_mem_sup {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ B)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ A ⊔ B) : ∀ w ∈ A ⊔ B, g * w * g⁻¹ ∈ A ⊔ B := by
  intro w hw
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => by simpa using hA a ha) (fun b hb => by simpa using hB b hb)
  simpa using h hw

theorem omegaOneCenter_inf_not_le (hA : F53Amalgam H M S) {δ δ' μ : Geo H M}
    (hμ : μ ∈ nbrs δ) (hle : stab δ ≤ (stab δ ⊓ stab μ) ⊔ Zv δ')
    (hn : ¬ Zv δ ≤ Qv δ') : ¬ quasithinOmegaOneCenter (stab δ ⊓ stab μ) ≤ Qv δ' := by
  intro hE
  have hT := sylow_stab_inf_left hA hμ
  have hcen : stab δ ≤ Subgroup.centralizer
      (quasithinOmegaOneCenter (stab δ ⊓ stab μ) : Set G) := by
    refine hle.trans (sup_le ?_ ?_)
    · intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact ((Subgroup.mem_centralizer_iff.mp
        (omegaOneCenter_le_inf_centralizer _ he).2) t ht).symm
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA δ' hy).2) e (hE he)
  apply hn
  rw [Zv_eq_conjClosure hT]
  refine conjClosure_le fun h hh z hz => ?_
  have hc : z * h = h * z := (Subgroup.mem_centralizer_iff.mp (hcen hh)) z hz
  have : h * z * h⁻¹ = z := by rw [← hc]; group
  rw [this]
  exact hE hz

theorem stab_le_normalizer_sup (hA : F53Amalgam H M S) {δ δ' μ : Geo H M}
    (hZ'δ : Zv δ' ≤ stab δ) (hle : stab δ ≤ (stab δ ⊓ stab μ) ⊔ Zv δ')
    (hcomm : ∀ x ∈ Zv μ, ∀ y ∈ Zv δ', y * x * y⁻¹ ∈ Zv δ ⊔ Zv μ) :
    stab δ ≤ Subgroup.normalizer ((Zv δ ⊔ Zv μ : Subgroup G) : Set G) := by
  have hnδ := stab_le_normalizer_Zv hA δ
  have hnμ := stab_le_normalizer_Zv hA μ
  have hδ : ∀ g ∈ stab δ, ∀ a ∈ Zv δ, g * a * g⁻¹ ∈ Zv δ ⊔ Zv μ := fun g hg a ha =>
    Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hnδ hg) a).mp ha)
  refine hle.trans (sup_le ?_ ?_)
  · intro t ht
    have hμ' : ∀ g ∈ stab μ, ∀ b ∈ Zv μ, g * b * g⁻¹ ∈ Zv δ ⊔ Zv μ := fun g hg b hb =>
      Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hnμ hg) b).mp hb)
    exact mem_normalizer_of_conj_le
      (conj_mem_sup (hδ t ht.1) (hμ' t ht.2))
      (conj_mem_sup (hδ t⁻¹ (Subgroup.inv_mem _ ht.1))
        (hμ' t⁻¹ (Subgroup.inv_mem _ ht.2)))
  · intro y hy
    exact mem_normalizer_of_conj_le
      (conj_mem_sup (hδ y (hZ'δ hy)) (fun b hb => hcomm b hb y hy))
      (conj_mem_sup (hδ y⁻¹ (hZ'δ (Subgroup.inv_mem _ hy)))
        (fun b hb => hcomm b hb y⁻¹ (Subgroup.inv_mem _ hy)))

theorem conj_mem_of_le_sup (hA : F53Amalgam H M S) {δ δ' μ : Geo H M}
    (hZδ : Zv δ ≤ stab δ') (hZ'δ : Zv δ' ≤ stab δ) (h1 : Zv μ ≤ Zv δ ⊔ Qv δ') :
    ∀ x ∈ Zv μ, ∀ y ∈ Zv δ', y * x * y⁻¹ ∈ Zv δ ⊔ Zv μ := by
  intro x hx y hy
  have hn : Zv δ ≤ Subgroup.normalizer (Qv δ' : Set G) :=
    hZδ.trans (le_normalizer_pCoreOf_of_le_normalizer Subgroup.le_normalizer)
  have hx' : x ∈ Qv δ' ⊔ Zv δ := by rw [sup_comm]; exact h1 hx
  obtain ⟨q, hq, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hn).mp hx'
  have hyq : y * q = q * y :=
    ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA δ' hy).2) q hq).symm
  have hyz : y * z * y⁻¹ ∈ Zv δ :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA δ (hZ'δ hy)) z).mp hz
  have e : y * (q * z) * y⁻¹ = (q * z) * z⁻¹ * (y * z * y⁻¹) := by
    calc y * (q * z) * y⁻¹ = (y * q) * z * y⁻¹ := by group
      _ = (q * y) * z * y⁻¹ := by rw [hyq]
      _ = (q * z) * z⁻¹ * (y * z * y⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hx)
    (Subgroup.mem_sup_left (Subgroup.inv_mem _ hz))) (Subgroup.mem_sup_left hyz)


theorem conj_mem_of_case2 (hA : F53Amalgam H M S) (h15 : Hss15) {δ δ' μ : Geo H M}
    (hv' : vtype δ' = false) (hb' : bAt δ' = bMin H M) (hμ : μ ∈ nbrs δ) (hvμ : vtype μ = true)
    (hZμδ' : Zv μ ≤ stab δ') (hZδ : Zv δ ≤ stab δ') (hZ'δ : Zv δ' ≤ stab δ)
    (hZμQ : Zv μ ≤ Qv δ) {s : G} (hsδ : s ∈ Zv δ) (hsμ : s ∈ Zv μ) (hsQ : s ∉ Qv δ')
    (h2' : (Zv δ' ⊓ Qv δ).relIndex (Zv δ') = 2)
    (h4 : (Zv μ ⊓ Qv δ').relIndex (Zv μ) = 4) :
    ∀ x ∈ Zv μ, ∀ y ∈ Zv δ', y * x * y⁻¹ ∈ Zv δ ⊔ Zv μ := by
  set V := Zv δ' with hVdef
  set K := V ⊓ Subgroup.centralizer ({s} : Set G) with hKdef
  have hDK : V ⊓ Qv δ ≤ K := fun d hd => ⟨hd.1, Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA δ hsδ).2) d hd.2)⟩
  have hKV : K ≤ V := inf_le_left
  have hKne : ¬ V ≤ K := by
    intro hle
    apply hsQ
    rw [← centralizer_Zv_eq_Qv_of_bAt hA hb']
    exact ⟨hZδ hsδ, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hv).2⟩
  have hmul := Subgroup.relIndex_mul_relIndex (V ⊓ Qv δ) K V hDK hKV
  rw [h2'] at hmul
  have hKi1 : K.relIndex V ≠ 1 := fun h => hKne (Subgroup.relIndex_eq_one.mp h)
  have hKi0 : K.relIndex V ≠ 0 := fun h => by rw [h, mul_zero] at hmul; omega
  have hKi : K.relIndex V = 2 := by
    have hdvd : K.relIndex V ∣ 2 := ⟨_, by rw [mul_comm] at hmul; exact hmul.symm⟩
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : K.relIndex V <;> simp_all
  have hDKeq : K ≤ Qv δ := by
    have h1 : (V ⊓ Qv δ).relIndex K = 1 := by
      rw [hKi] at hmul; omega
    exact fun k hk => ((Subgroup.relIndex_eq_one.mp h1) hk).2
  obtain ⟨u, huμ, hgen, hnot⟩ := exists_partner h15 (quot_stab_five hA hv')
    (Zv_le_Qv hA δ') (stab_le_normalizer_Zv hA δ') (isElemAbelian_Zv hA δ')
    (centralizer_Zv_eq_Qv_of_bAt hA hb') hsμ hKi hZμδ' (isElemAbelian_Zv hA μ) h4
  obtain ⟨c, ⟨hcV, hcu⟩, hcK⟩ := Set.not_subset.mp hnot
  have hcu' : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hcu
  have hQT : Qv δ ≤ stab δ ⊓ stab μ := le_inf (pCoreOf_le 2 _) (Qv_le_stab_of_mem_nbrs hA hμ)
  have hδμ : δ ∈ nbrs μ := (show (graph (H ⊔ M) H M).Adj δ μ from hμ).symm
  have hTZ : ∀ d ∈ stab δ ⊓ stab μ, ∀ x ∈ Zv μ, d * x * d⁻¹ * x⁻¹ ∈ Zv δ := by
    intro d hd x hx
    have h1 : d * x * d⁻¹ * x⁻¹ ∈ ⁅Zv μ, stab δ ⊓ stab μ⁆ := by
      rw [Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator hd hx
      rwa [commutatorElement_def] at this
    exact (omegaOneCenter_le_Zv hA hμ).2.1 (commutator_Zv_inf_le hA hvμ hδμ h1)
  have hZμδ : Zv μ ≤ stab δ := hZμQ.trans (pCoreOf_le 2 _)
  have hconjδ : ∀ g ∈ stab δ, ∀ z ∈ Zv δ, g * z * g⁻¹ ∈ Zv δ := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA δ hg) z).mp hz
  let P : Subgroup G :=
    { carrier := {x | x ∈ Zv μ ∧ ∀ y ∈ V, y * x * y⁻¹ * x⁻¹ ∈ Zv δ}
      one_mem' := ⟨Subgroup.one_mem _, fun y _ => by simp⟩
      mul_mem' := fun {x₁ x₂} h₁ h₂ => ⟨Subgroup.mul_mem _ h₁.1 h₂.1, fun y hy => by
        have e : y * (x₁ * x₂) * y⁻¹ * (x₁ * x₂)⁻¹ =
            (y * x₁ * y⁻¹ * x₁⁻¹) * (x₁ * (y * x₂ * y⁻¹ * x₂⁻¹) * x₁⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (h₁.2 y hy) (hconjδ _ (hZμδ h₁.1) _ (h₂.2 y hy))⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, fun y hy => by
        have e : y * x⁻¹ * y⁻¹ * x⁻¹⁻¹ = x⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact hconjδ _ (Subgroup.inv_mem _ (hZμδ hx.1)) _ (Subgroup.inv_mem _ (hx.2 y hy))⟩ }
  have hsP : s ∈ P := ⟨hsμ, fun y hy => Subgroup.mul_mem _ (hconjδ y (hZ'δ hy) s hsδ)
    (Subgroup.inv_mem _ hsδ)⟩
  have hqP : Zv μ ⊓ Qv δ' ≤ P := fun q hq => ⟨hq.1, fun y hy => by
    have hyq : y * q = q * y :=
      ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA δ' hy).2) q hq.2).symm
    have : y * q * y⁻¹ * q⁻¹ = 1 := by rw [hyq]; group
    rw [this]; exact Subgroup.one_mem _⟩
  have huP : u ∈ P := ⟨huμ, fun y hy => by
    have hidx : (K.subgroupOf V).index = 2 := hKi
    have hyc := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y, hy⟩) (b := ⟨c, hcV⟩))
    by_cases hyK : y ∈ K
    · exact hTZ y (hQT (hDKeq hyK)) u huμ
    · have hycK : y * c ∈ K := by
        have : (⟨y * c, Subgroup.mul_mem _ hy hcV⟩ : ↥V) ∈ K.subgroupOf V := by
          rw [show (⟨y * c, Subgroup.mul_mem _ hy hcV⟩ : ↥V) = ⟨y, hy⟩ * ⟨c, hcV⟩ from rfl, hyc]
          exact ⟨fun h => absurd h hyK, fun h => absurd h hcK⟩
        exact this
      have e : y * u * y⁻¹ * u⁻¹ = (y * c) * u * (y * c)⁻¹ * u⁻¹ := by
        have : c * u * c⁻¹ = u := by rw [hcu']; group
        calc y * u * y⁻¹ * u⁻¹ = y * (c * u * c⁻¹) * y⁻¹ * u⁻¹ := by rw [this]
          _ = (y * c) * u * (y * c)⁻¹ * u⁻¹ := by group
      rw [e]
      exact hTZ _ (hQT (hDKeq hycK)) u huμ⟩
  have hμP : Zv μ ≤ P := by
    refine hgen.trans (sup_le ?_ hqP)
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hsP
    · exact huP
  intro x hx y hy
  have h := (hμP hx).2 y hy
  have e : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right hx)


structure Pair41 (δ δ' : Geo H M) : Prop where
  vδ : vtype δ = false
  vδ' : vtype δ' = false
  bδ : bAt δ = bMin H M
  bδ' : bAt δ' = bMin H M
  dist_eq : dist δ δ' = bMin H M
  nle : ¬ Zv δ ≤ Qv δ'
  nle' : ¬ Zv δ' ≤ Qv δ
  b2 : 2 ≤ bMin H M
  s3 : ∀ ν : Geo H M, vtype ν = true → bMin H M < bAt ν

omit [Finite G] in
theorem Pair41.symm {δ δ' : Geo H M} (P : Pair41 δ δ') : Pair41 δ' δ :=
  ⟨P.vδ', P.vδ, P.bδ', P.bδ, by rw [CosetGeom.dist_comm]; exact P.dist_eq, P.nle', P.nle, P.b2,
    P.s3⟩

theorem Pair41.Zv_le_stab (hA : F53Amalgam H M S) {δ δ' : Geo H M} (P : Pair41 δ δ') :
    Zv δ ≤ stab δ' :=
  Zv_le_stab_of_dist_le hA (by rw [P.dist_eq, P.bδ])

omit [Finite G] in
theorem Pair41.vtype_nbr {δ δ' μ : Geo H M} (P : Pair41 δ δ') (hμ : μ ∈ nbrs δ) :
    vtype μ = true := by
  have h := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from hμ)
  rw [P.vδ] at h
  cases hv : vtype μ
  · exact absurd hv.symm h
  · rfl

theorem Pair41.Zv_nbr_le_stab (hA : F53Amalgam H M S) {δ δ' μ : Geo H M} (P : Pair41 δ δ')
    (hμ : μ ∈ nbrs δ) : Zv μ ≤ stab δ' := by
  have hb := P.s3 μ (P.vtype_nbr hμ)
  have hadj : (graph (H ⊔ M) H M).Adj μ δ := (show (graph (H ⊔ M) H M).Adj δ μ from hμ).symm
  have h1 := dist_triangle_of_adj hadj δ'
  rw [dist_eq_one_iff_adj.mpr hadj, P.dist_eq] at h1
  exact Zv_le_stab_of_dist_le hA (by omega)

omit [Finite G] in
theorem Pair41.Zv_nbr_le_Qv {δ δ' μ : Geo H M} (P : Pair41 δ δ')
    (hμ : μ ∈ nbrs δ) : Zv μ ≤ Qv δ := by
  have hb := P.s3 μ (P.vtype_nbr hμ)
  have hadj : (graph (H ⊔ M) H M).Adj μ δ := (show (graph (H ⊔ M) H M).Adj δ μ from hμ).symm
  have hd : dist μ δ = 1 := dist_eq_one_iff_adj.mpr hadj
  have := P.b2
  exact Zv_le_Qv_of_dist_lt (by omega)

theorem Pair41.step (hA : F53Amalgam H M S) {δ δ' : Geo H M} (P : Pair41 δ δ') :
    ∃ μ ∈ nbrs δ, stab δ ≤ (stab δ ⊓ stab μ) ⊔ Zv δ' ∧
      ((∀ x ∈ Zv μ, ∀ y ∈ Zv δ', y * x * y⁻¹ ∈ Zv δ ⊔ Zv μ) ∨
        ((Zv δ ⊓ Qv δ').relIndex (Zv δ) = 2 ∧ (Zv μ ⊓ Qv δ').relIndex (Zv μ) = 4 ∧
          ∃ s ∈ Zv δ, s ∈ Zv μ ∧ s ∉ Qv δ')) := by
  have hY : Zv δ' ≤ stab δ := P.symm.Zv_le_stab hA
  obtain ⟨μ, hμ, hle⟩ := exists_nbr_le_sup hA P.vδ hY P.nle'
  refine ⟨μ, hμ, hle, ?_⟩
  have hZδ := P.Zv_le_stab hA
  have hZμ := P.Zv_nbr_le_stab hA hμ
  by_cases h1 : Zv μ ≤ Zv δ ⊔ Qv δ'
  · exact Or.inl (conj_mem_of_le_sup hA hZδ hY h1)
  right
  have hQn : stab δ' ≤ Subgroup.normalizer (Qv δ' : Set G) :=
    le_normalizer_pCoreOf_of_le_normalizer Subgroup.le_normalizer
  have hcomm : ∀ a ∈ Zv δ, ∀ b ∈ Zv μ, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA δ ha).2) b
      (P.Zv_nbr_le_Qv hμ hb)).symm
  have hE := isElemAbelian_sup_of_commute' (isElemAbelian_Zv hA δ) (isElemAbelian_Zv hA μ) hcomm
  have hE4 := relIndex_le_four_of_elemAbelian (quot_stab_five hA P.vδ') (sup_le hZδ hZμ) hE
  have hD := omegaOneCenter_inf_not_le hA hμ hle P.nle
  have hAC : ¬ Zv δ ⊓ Zv μ ≤ Qv δ' := fun h =>
    hD ((le_inf (omegaOneCenter_le_Zv hA hμ).2.1 (omegaOneCenter_le_Zv hA hμ).2.2).trans h)
  have h2 : ∀ (K : Subgroup G), IsElemAbelian 2 K → IsPGroup 2 K := fun K hK x =>
    ⟨1, Subtype.ext (by simpa using hK.2 x x.2)⟩
  obtain ⟨hδ2, hμ4, -⟩ := relIndex_two_four_of_not_le hQn hZδ hZμ
    (h2 _ (isElemAbelian_Zv hA δ)) hE4 P.nle hAC h1
  obtain ⟨s, ⟨hsδ, hsμ⟩, hsQ⟩ := Set.not_subset.mp hAC
  exact ⟨hδ2, hμ4, s, hsδ, hsμ, hsQ⟩

theorem hss41At_of (hA : F53Amalgam H M S) (h27 : Hss27S5At H M) (h15 : Hss15) :
    Hss41At H M := by
  intro α β hαβ hα hαb hβb
  obtain ⟨α', hc⟩ := exists_critData hA hαb hαβ
  by_cases hz : ⁅Zv α, Zv α'⁆ = ⊥
  · exact Zv_central_of_comm_eq_bot hA hc hz
  have heven := hss113_d hA hc hz hβb
  have hb1 := bMin_pos hA
  have hb2 : 2 ≤ bMin H M := by obtain ⟨k, hk⟩ := heven; omega
  have hβv : vtype β = true := by
    have h := vtype_ne_of_adj hαβ
    rw [hα] at h
    cases hv : vtype β
    · exact absurd hv.symm h
    · rfl
  have hS3 : ∀ ν : Geo H M, vtype ν = true → bMin H M < bAt ν := fun ν hν => by
    rw [bAt_eq_of_vtype_eq (hν.trans hβv.symm)]; exact hβb
  obtain ⟨-, hα'b⟩ := crit_bAt_eq hA ⟨hc.not_le, hc.dist_eq⟩ hz
  have hαα' : vtype α = vtype α' := by
    rw [vtype_eq_iff_even_dist hA.amalgam.gen, hc.dist_eq]; exact heven
  have hn' : ¬ Zv α' ≤ Qv α := by
    intro hle
    apply hz
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun x hx => Subgroup.centralizer_le hle ((Zv_le_centerOf_Qv hA α hx).2)
  have P : Pair41 α α' :=
    ⟨hα, hαα' ▸ hα, hαb, hα'b, hc.dist_eq, hc.not_le, hn', hb2, hS3⟩
  have key : ∀ {δ δ' : Geo H M}, Pair41 δ δ' → ∀ μ ∈ nbrs δ,
      stab δ ≤ Subgroup.normalizer ((Zv δ ⊔ Zv μ : Subgroup G) : Set G) →
      Zv β ≤ centerOf (stab β) := by
    intro δ δ' Q μ hμ hN
    have h := h27 hb2 δ μ hμ Q.vδ Q.bδ hN
    exact Zv_central_of_vtype_eq hA ((Q.vtype_nbr hμ).trans hβv.symm) h
  obtain ⟨μ, hμ, hle, hcase⟩ := P.step hA
  obtain ⟨μ', hμ', hle', hcase'⟩ := P.symm.step hA
  rcases hcase with h1 | ⟨-, h4, s, hsδ, hsμ, hsQ⟩
  · exact key P μ hμ (stab_le_normalizer_sup hA (P.symm.Zv_le_stab hA) hle h1)
  rcases hcase' with h1' | ⟨h2', -, -⟩
  · exact key P.symm μ' hμ' (stab_le_normalizer_sup hA (P.Zv_le_stab hA) hle' h1')
  exact key P μ hμ (stab_le_normalizer_sup hA (P.symm.Zv_le_stab hA) hle
    (conj_mem_of_case2 hA h15 P.vδ' P.bδ' hμ (P.vtype_nbr hμ) (P.Zv_nbr_le_stab hA hμ)
      (P.Zv_le_stab hA) (P.symm.Zv_le_stab hA) (P.Zv_nbr_le_Qv hμ) hsδ hsμ hsQ h2' h4))

end F53.Stellmacher

end CFSG.Quasithin
