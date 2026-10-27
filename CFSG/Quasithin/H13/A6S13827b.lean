module

public import CFSG.Quasithin.H13.A6S13827a
public import CFSG.Quasithin.H13.A6S13829a
public import CFSG.Quasithin.H13.A6S13834P

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

theorem swap_V2_facts : act4f (swap 0 4 * swap 1 5) e0123 = dv 0 1 ∧
    act4f (swap 2 4 * swap 3 5) e0123 = dv 2 3 ∧
    swap (0 : Fin 6) 4 * swap 1 5 ∈ alternatingGroup (Fin 6) ∧
    swap (2 : Fin 6) 4 * swap 3 5 ∈ alternatingGroup (Fin 6) ∧
    swap (0 : Fin 6) 4 * swap 1 5 * (swap 0 4 * swap 1 5) = 1 ∧
    swap (2 : Fin 6) 4 * swap 3 5 * (swap 2 4 * swap 3 5) = 1 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide⟩ <;>
    rw [Equiv.Perm.mem_alternatingGroup] <;> decide

theorem exists_GL_vec {a b : Fin 4 → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ M : GL (Fin 4) (ZMod 2), (M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec a = b := by
  obtain ⟨a', ha'⟩ := exists_not_mem_list [0, a] (by simp)
  obtain ⟨b', hb'⟩ := exists_not_mem_list [0, b] (by simp)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at ha' hb'
  obtain ⟨c, d, hcd⟩ := exists_basis_of_pair ha ha'.1 (Ne.symm ha'.2)
  obtain ⟨c', d', hcd'⟩ := exists_basis_of_pair hb hb'.1 (Ne.symm hb'.2)
  obtain ⟨M, hM, -⟩ := exists_GL_map4 hcd hcd'
  exact ⟨M, hM⟩

@[expose] def DuadList : List (Perm (Fin 6)) :=
  [1, swap 1 2 * swap 4 5, swap 1 2 * swap 2 3, swap 1 2 * swap 2 3 * swap 3 5 * swap 5 4,
    swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5, swap 0 2 * swap 2 1,
    swap 0 2 * swap 2 3 * swap 3 1 * swap 4 5, swap 0 2 * swap 2 3 * swap 3 4 * swap 4 1,
    swap 0 2 * swap 2 3 * swap 3 5 * swap 5 1, swap 0 2 * swap 1 3,
    swap 0 2 * swap 1 3 * swap 3 5 * swap 5 4, swap 0 2 * swap 1 3 * swap 3 4 * swap 4 5,
    swap 0 2 * swap 2 4 * swap 4 1 * swap 1 3, swap 0 2 * swap 2 4 * swap 4 5 * swap 1 3,
    swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5]

theorem duadList_mem : ∀ σ ∈ DuadList, σ ∈ alternatingGroup (Fin 6) := by
  intro σ hσ
  rw [Equiv.Perm.mem_alternatingGroup]
  revert σ
  decide +kernel

@[expose] def e01v : Fin 6 → ZMod 2 := ![1, 1, 0, 0, 0, 0]

theorem duad_trans : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 → x ≠ 0 → x ≠ onesV →
    ∃ σ ∈ DuadList, vp σ x = e01v ∨ vp σ x = e01v + onesV := by
  decide +kernel

@[expose] def wt2v (i j : Fin 6) : Fin 6 → ZMod 2 := fun k => if k = i ∨ k = j then 1 else 0

@[expose] def dwt2 (σ : Perm (Fin 6)) (k l : Fin 6) : Fin 6 → ZMod 2 := vp σ (wt2v k l) + wt2v k l

@[expose] def TvOn6 (σ : Perm (Fin 6)) (c : Fin 6 → ZMod 2) : Prop :=
  ∀ k l : Fin 6, k < l → dwt2 σ k l = 0 ∨ dwt2 σ k l = c

instance (σ : Perm (Fin 6)) (c : Fin 6 → ZMod 2) : Decidable (TvOn6 σ c) := by
  unfold TvOn6
  infer_instance

theorem tv6_swap : ∀ σ : Perm (Fin 6), ∀ k₀ l₀ : Fin 6, k₀ < l₀ → dwt2 σ k₀ l₀ ≠ 0 →
    TvOn6 σ (dwt2 σ k₀ l₀) → ∃ i j : Fin 6, i < j ∧ σ = swap i j ∧ dwt2 σ k₀ l₀ = wt2v i j := by
  decide +kernel

theorem tv6_axis : ∀ i j : Fin 6, i < j → ∀ σ : Perm (Fin 6),
    (∀ k l : Fin 6, k < l → wt2v k l i = wt2v k l j →
      dwt2 σ k l = 0 ∨ dwt2 σ k l = wt2v i j) → σ = 1 ∨ σ = swap i j := by
  decide +kernel

theorem exists_dwt2_ne : ∀ σ : Perm (Fin 6), σ ≠ 1 → ∃ k l : Fin 6, k < l ∧ dwt2 σ k l ≠ 0 := by
  decide +kernel

theorem wt2v_facts : (∀ i j : Fin 6, i < j → ∑ k, wt2v i j k = 0) ∧
    (∀ i j i' j' : Fin 6, i < j → i' < j' → wt2v i j = wt2v i' j' → swap i j = swap i' j') ∧
    (∀ i j k l : Fin 6, wt2v k l i = wt2v k l j → vp (swap i j) (wt2v k l) = wt2v k l) :=
  ⟨by decide, by decide, by decide⟩

theorem fixMod_cases : ∀ σ : Perm (Fin 6), (∀ x : P6, InW4 x →
    act4f σ x * x⁻¹ = 1 ∨ act4f σ x * x⁻¹ = e0123) → σ = 1 ∨ σ = swap 4 5 := by
  decide +kernel

theorem fixW3_one_swap45 : FixW3 1 ∧ FixW3 (swap 4 5) := ⟨by decide, t_facts.1⟩

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_swap {x : G}
    (hUQ : conjClosure S.V3 S.G1 ≤ conjSub x (pCoreOf 2 S.G1))
    (hXQ : ¬ conjSub x (conjClosure S.V3 S.G1) ≤ pCoreOf 2 S.G1) {h : G} (hh : h ∈ S.G1)
    (hb : h * (x * S.z * x⁻¹) * h⁻¹ ∈ S.V2) (hb1 : h * (x * S.z * x⁻¹) * h⁻¹ ∉ fsuV1 T V) :
    False := by
  set b := h * (x * S.z * x⁻¹) * h⁻¹ with hbdef
  obtain ⟨hbV, hbW⟩ := S.mem_pre.1 hb
  have hbW' : InW2 (S.frame.ψ ⟨b, hbV⟩ : P6) := hbW
  have hb1' : (S.frame.ψ ⟨b, hbV⟩ : P6) ≠ 1 ∧ (S.frame.ψ ⟨b, hbV⟩ : P6) ≠ e0123 := by
    constructor
    · intro h1
      apply hb1
      have : (⟨b, hbV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h1)
      rw [show b = 1 from congrArg Subtype.val this]
      exact (fsuV1 T V).one_mem
    · intro h1
      apply hb1
      have : (⟨b, hbV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
        S.frame.ψ.injective (by rw [S.psi_z]; exact Subtype.ext h1)
      rw [show b = S.z from congrArg Subtype.val this]
      exact S.mem_V1_iff.2 (Or.inr rfl)
  obtain ⟨l, -, hlz, hll⟩ : ∃ l : ↥(Subgroup.normalizer (V : Set G)), (l : G) ∈ L ∧
      (l : G) * S.z * (l : G)⁻¹ = b ∧ (l : G) * l ∈ S.G1 := by
    obtain ⟨f1, f2, a1, a2, s1, s2⟩ := swap_V2_facts
    have key : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) → σ * σ = 1 →
        act4f σ e0123 = (S.frame.ψ ⟨b, hbV⟩ : P6) →
        ∃ l : ↥(Subgroup.normalizer (V : Set G)), (l : G) ∈ L ∧
          (l : G) * S.z * (l : G)⁻¹ = b ∧ (l : G) * l ∈ S.G1 := by
      intro σ hσ hσ2 hσb
      obtain ⟨l, hlL, hρl⟩ := (S.frame.image_L σ).2 hσ
      refine ⟨l, hlL, ?_, ?_⟩
      · have h1 := S.psi_conj l ⟨S.z, S.z_mem_V⟩
        have h2 : S.frame.ψ ⟨(l : G) * S.z * (l : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp l.2 S.z).mp S.z_mem_V⟩ = S.frame.ψ ⟨b, hbV⟩ := by
          rw [h1, S.psi_z]
          apply Subtype.ext
          rw [act4_coe, hρl]
          exact hσb
        exact congrArg Subtype.val (S.frame.ψ.injective h2)
      · have h1 := (S.conj_eq_iff (l * l) ⟨S.z, S.z_mem_V⟩).2 (by
          rw [map_mul, hρl, hσ2, map_one, MulAut.one_apply])
        rw [G1, Subgroup.mem_centralizer_singleton_iff]
        have e : (l : G) * l * S.z = (l : G) * l * S.z * ((l : G) * l)⁻¹ * ((l : G) * l) := by
          group
        rw [e]
        exact congrArg (· * ((l : G) * l)) h1
    rcases hbW' with h1 | h1 | h1 | h1
    · exact absurd h1 hb1'.1
    · exact key _ a1 s1 (by rw [f1, h1])
    · exact key _ a2 s2 (by rw [f2, h1])
    · exact absurd h1 hb1'.2
  have hn : (l : G)⁻¹ * h * x ∈ S.G1 := by
    rw [G1, Subgroup.mem_centralizer_singleton_iff]
    have e1 : (l : G)⁻¹ * b * l = S.z := by
      rw [← hlz]
      group
    calc (l : G)⁻¹ * h * x * S.z = (l : G)⁻¹ * b * (l : G) * ((l : G)⁻¹ * h * x) := by
          rw [hbdef]; group
      _ = S.z * ((l : G)⁻¹ * h * x) := by rw [e1]
  have hUN : ∀ k ∈ S.G1, conjSub k (conjClosure S.V3 S.G1) = conjClosure S.V3 S.G1 :=
    fun k hk => F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 S.G1 hk)
  have hQN : ∀ k ∈ S.G1, conjSub k (pCoreOf 2 S.G1) = pCoreOf 2 S.G1 :=
    fun k hk => F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 S.G1 hk)
  have hx : x = h⁻¹ * (l : G) * ((l : G)⁻¹ * h * x) := by group
  apply hXQ
  rw [hx, conjSub_mul, conjSub_mul, hUN _ hn]
  have h1 : conjSub (l : G) (conjClosure S.V3 S.G1) ≤ pCoreOf 2 S.G1 := by
    have h2 := hUQ
    rw [hx, conjSub_mul, conjSub_mul, hQN _ hn] at h2
    have h3 := conjSub_mono h h2
    rw [hUN h hh, ← conjSub_mul, mul_inv_cancel, conjSub_one] at h3
    have h4 := conjSub_mono (l : G) h3
    rw [← conjSub_mul, hQN _ hll] at h4
    exact h4
  have h5 := conjSub_mono h⁻¹ h1
  rwa [hQN _ (S.G1.inv_mem hh)] at h5

theorem caseB_data (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
    (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) < conjClosure S.V3 S.G1) :
    conjClosure S.V3 S.G1 ≤ conjSub (g : G)⁻¹ (pCoreOf 2 S.G1) ∧
      ¬ conjSub (g : G)⁻¹ (conjClosure S.V3 S.G1) ≤ pCoreOf 2 S.G1 ∧
      conjSub (g : G)⁻¹ (conjClosure S.V3 S.G1) ≤ S.G1 ∧
      ⁅conjSub (g : G)⁻¹ (conjClosure S.V3 S.G1), conjClosure S.V3 S.G1⁆ =
        conjSub (g : G)⁻¹ (fsuV1 T V) := by
  have hUγ : conjSub (g : G)⁻¹ (F8.Uγ S.V3 S.G1 (g : G)) = conjClosure S.V3 S.G1 := by
    rw [F8.Uγ, conjSub_conjSub_inv]
  have hstab : stab γ = conjSub (g : G) S.G1 := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
  have hUst : conjClosure S.V3 S.G1 ≤ stab γ :=
    (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans
      inf_le_right))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : F8.Uγ S.V3 S.G1 (g : G) ≤ pCoreOf 2 S.G1 := by
      have := hF.Dγ_eq_inf_pCoreOf s
      rw [hDγ] at this
      exact inf_eq_left.mp this.symm
    have h2 := conjSub_mono (g : G)⁻¹ h1
    rwa [hUγ] at h2
  · intro hle
    apply (lt_iff_le_not_ge.mp hDH).2
    intro u hu
    have hq : (g : G)⁻¹ * u * (g : G) ∈ pCoreOf 2 S.G1 := by
      have := hle (mul_mem_conjSub (g := (g : G)⁻¹) hu)
      rwa [inv_inv] at this
    rw [hF.toHypF91.pCoreOf_eq_centralizerMod] at hq
    obtain ⟨-, hqN, hqc⟩ := hq
    refine ⟨hu, ?_, fun w hw => ?_⟩
    · rw [F8.A₁, Subgroup.mem_normalizer_iff]
      intro y
      rw [mem_conjSub, mem_conjSub]
      have h1 := Subgroup.mem_normalizer_iff.mp hqN ((g : G)⁻¹ * y * g)
      have e : (g : G)⁻¹ * (u * y * u⁻¹) * g = ((g : G)⁻¹ * u * g) * ((g : G)⁻¹ * y * g) *
          ((g : G)⁻¹ * u * g)⁻¹ := by group
      rw [e]
      exact h1
    · have hw' : (g : G)⁻¹ * w * (g : G) ∈ conjClosure S.V3 S.G1 := mem_conjSub.mp hw
      have h1 := hqc _ hw'
      rw [F8.A₁, mem_conjSub]
      have e : (g : G)⁻¹ * (u * w * u⁻¹ * w⁻¹) * g = ((g : G)⁻¹ * u * g) *
          ((g : G)⁻¹ * w * g) * ((g : G)⁻¹ * u * g)⁻¹ * ((g : G)⁻¹ * w * g)⁻¹ := by group
      rw [e]
      exact h1
  · rw [conjSub_le_iff, inv_inv, ← hstab]
    exact hUst
  · rcases hF.F916_1 s hDγ.symm with ⟨-, htr⟩ | ⟨hDH', -⟩
    · rw [← htr.2.2, ← conjSub_commutator, hUγ]
    · exact absurd hDH' (ne_of_lt hDH)

theorem caseB_a (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    (hXG : conjSub (g : G)⁻¹ (conjClosure S.V3 S.G1) ≤ S.G1)
    (hcomm : ⁅conjSub (g : G)⁻¹ (conjClosure S.V3 S.G1), conjClosure S.V3 S.G1⁆ =
      conjSub (g : G)⁻¹ (fsuV1 T V)) :
    (g : G)⁻¹ * S.z * (g : G)⁻¹⁻¹ ∈ conjClosure S.V3 S.G1 ∧
      (g : G)⁻¹ * S.z * (g : G)⁻¹⁻¹ ∉ fsuV1 T V := by
  have hzV1 : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have ha : (g : G)⁻¹ * S.z * (g : G)⁻¹⁻¹ ∈ conjSub (g : G)⁻¹ (fsuV1 T V) :=
    mul_mem_conjSub hzV1
  refine ⟨?_, fun h1 => ?_⟩
  · rw [← hcomm] at ha
    refine (Subgroup.commutator_le.2 fun p hp q hq => ?_) ha
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure S.V3 S.G1 (hXG hp)) q).mp hq) (Subgroup.inv_mem _ hq)
  · have h5 := hF.F913_5b s
    have h6 : fsuV1 T V ⊓ conjSub (g : G)⁻¹ (fsuV1 T V) = ⊥ := by
      have := congrArg (conjSub (g : G)⁻¹) h5
      rwa [conjSub_inf, F8.A₁, conjSub_conjSub_inv, conjSub_bot, inf_comm] at this
    have h7 : (g : G)⁻¹ * S.z * (g : G)⁻¹⁻¹ ∈ fsuV1 T V ⊓ conjSub (g : G)⁻¹ (fsuV1 T V) :=
      ⟨h1, ha⟩
    rw [h6, Subgroup.mem_bot] at h7
    apply S.z_ne_one
    calc S.z = (g : G) * ((g : G)⁻¹ * S.z * (g : G)⁻¹⁻¹) * (g : G)⁻¹ := by group
      _ = 1 := by rw [h7]; group

theorem exists_conj_V2_hat {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
    (hρs : Function.Surjective ρ)
    {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}
    (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) =
        ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u)))
    {a : G} (ha : a ∈ conjClosure S.V3 S.G1) (haV : a ∉ fsuV1 T V) :
    ∃ h ∈ S.G1, h * a * h⁻¹ ∈ S.V2 ∧ h * a * h⁻¹ ∉ fsuV1 T V := by
  have hu1 : S.u1 ∈ conjClosure S.V3 S.G1 := le_conjClosure S.V3 S.G1 S.u1_mem_V3
  have hne : ∀ (w : G) (hw : w ∈ conjClosure S.V3 S.G1), w ∉ fsuV1 T V →
      Multiplicative.toAdd (β ⟨w, hw⟩) ≠ 0 := fun w hw hwV h0 =>
    hwV ((hβk ⟨w, hw⟩).1 (by rw [← ofAdd_toAdd (β ⟨w, hw⟩), h0, ofAdd_zero]))
  obtain ⟨M, hM⟩ := exists_GL_vec (hne a ha haV) (hne _ hu1 S.u1_not_V1)
  obtain ⟨h, rfl⟩ := hρs M
  have hhaU : (h : G) * a * (h : G)⁻¹ ∈ conjClosure S.V3 S.G1 :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 h.2) a).mp ha
  have he := hβe h ⟨a, ha⟩ ⟨_, hhaU⟩ rfl
  rw [hM] at he
  have hq : (h : G) * a * (h : G)⁻¹ * S.u1⁻¹ ∈ fsuV1 T V := by
    have := (hβk (⟨_, hhaU⟩ * (⟨S.u1, hu1⟩ : ↥(conjClosure S.V3 S.G1))⁻¹)).1 (by
      rw [map_mul, map_inv, ← ofAdd_toAdd (β ⟨_, hhaU⟩), he, ofAdd_toAdd]
      exact mul_inv_cancel _)
    exact this
  refine ⟨h, h.2, ?_, fun h1 => ?_⟩
  · have e : (h : G) * a * (h : G)⁻¹ = ((h : G) * a * (h : G)⁻¹ * S.u1⁻¹) * S.u1 := by group
    rw [e]
    exact S.V2.mul_mem (S.V1_le_V2 hq) S.u1_mem_V2
  · apply S.u1_not_V1
    have e : S.u1 = ((h : G) * a * (h : G)⁻¹ * S.u1⁻¹)⁻¹ * ((h : G) * a * (h : G)⁻¹) := by
      group
    rw [e]
    exact (fsuV1 T V).mul_mem ((fsuV1 T V).inv_mem hq) h1

theorem exists_conj_V2_nat {K : Subgroup G} {ρ : ↥S.G1 →* Perm (Fin 6)}
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)}
    (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) =
        Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
    {a : G} (ha : a ∈ conjClosure S.V3 S.G1) (haV : a ∉ fsuV1 T V) :
    ∃ h ∈ S.G1, h * a * h⁻¹ ∈ S.V2 ∧ h * a * h⁻¹ ∉ fsuV1 T V := by
  have hu1 : S.u1 ∈ conjClosure S.V3 S.G1 := le_conjClosure S.V3 S.G1 S.u1_mem_V3
  have hrep : ∀ (w : G) (hw : w ∈ conjClosure S.V3 S.G1), w ∉ fsuV1 T V →
      ∃ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) =
        Multiplicative.toAdd (β ⟨w, hw⟩) ∧ (x : Fin 6 → ZMod 2) ≠ 0 ∧
        (x : Fin 6 → ZMod 2) ≠ onesV := by
    intro w hw hwV
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β ⟨w, hw⟩))
    have hx0 : (QuotientAddGroup.mk x : AltHeart 6) ≠ 0 := by
      rw [hx]
      intro h0
      exact hwV ((hβk ⟨w, hw⟩).1 (by rw [← ofAdd_toAdd (β ⟨w, hw⟩), h0, ofAdd_zero]))
    rw [Ne, mk_eq_zero_iff, not_or] at hx0
    exact ⟨x, hx, hx0⟩
  obtain ⟨xa, hxa, hxa0, hxa1⟩ := hrep a ha haV
  obtain ⟨x1, hx1, hx10, hx11⟩ := hrep _ hu1 S.u1_not_V1
  obtain ⟨σa, hσa, hσxa⟩ := duad_trans _ (sum_eq_zero xa) hxa0 hxa1
  obtain ⟨σ1, hσ1, hσx1⟩ := duad_trans _ (sum_eq_zero x1) hx10 hx11
  have hτ : σ1⁻¹ * σa ∈ alternatingGroup (Fin 6) :=
    (alternatingGroup (Fin 6)).mul_mem ((alternatingGroup (Fin 6)).inv_mem (duadList_mem _ hσ1))
      (duadList_mem _ hσa)
  have hvτ : vp (σ1⁻¹ * σa) xa = x1 ∨ vp (σ1⁻¹ * σa) xa = (x1 : Fin 6 → ZMod 2) + onesV := by
    have e1 := vp_inv_vp σ1 (x1 : Fin 6 → ZMod 2)
    have hones : vp σ1⁻¹ onesV = onesV := rfl
    rw [vp_mul]
    rcases hσxa with h1 | h1 <;> rcases hσx1 with h2 | h2 <;> rw [h1]
    · left
      rw [← h2, e1]
    · right
      rw [show e01v = vp σ1 x1 + onesV by rw [h2, add_assoc, vadd_self, add_zero], vp_add, e1,
        hones]
    · right
      rw [← h2, vp_add, e1, hones]
    · left
      rw [← h2, e1]
  obtain ⟨k, -, hk⟩ := honto _ hτ
  have hkaU : (k : G) * a * (k : G)⁻¹ ∈ conjClosure S.V3 S.G1 :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 k.2) a).mp ha
  have he := hβe k ⟨a, ha⟩ ⟨_, hkaU⟩ rfl xa hxa
  have he' : Multiplicative.toAdd (β ⟨_, hkaU⟩) = Multiplicative.toAdd (β ⟨S.u1, hu1⟩) := by
    rw [← he, ← hx1, mk_eq_mk_iff, hk]
    exact hvτ
  have hq : (k : G) * a * (k : G)⁻¹ * S.u1⁻¹ ∈ fsuV1 T V := by
    have := (hβk (⟨_, hkaU⟩ * (⟨S.u1, hu1⟩ : ↥(conjClosure S.V3 S.G1))⁻¹)).1 (by
      rw [map_mul, map_inv, ← ofAdd_toAdd (β ⟨_, hkaU⟩), he', ofAdd_toAdd]
      exact mul_inv_cancel _)
    exact this
  refine ⟨k, k.2, ?_, fun h1 => ?_⟩
  · have e : (k : G) * a * (k : G)⁻¹ = ((k : G) * a * (k : G)⁻¹ * S.u1⁻¹) * S.u1 := by group
    rw [e]
    exact S.V2.mul_mem (S.V1_le_V2 hq) S.u1_mem_V2
  · apply S.u1_not_V1
    have e : S.u1 = ((k : G) * a * (k : G)⁻¹ * S.u1⁻¹)⁻¹ * ((k : G) * a * (k : G)⁻¹) := by
      group
    rw [e]
    exact (fsuV1 T V).mul_mem ((fsuV1 T V).inv_mem hq) h1

theorem false_caseB_cover_core (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz)
    (hab : IsMulCommutative ↥(conjClosure V S.G1)) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {ρ : ↥S.G1 →* Perm (Fin 6)} (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
    (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
    {x : G} (hUQ : conjClosure S.V3 S.G1 ≤ conjSub x (pCoreOf 2 S.G1))
    (hXG : conjSub x (conjClosure S.V3 S.G1) ≤ S.G1)
    (hVG : conjSub x (conjClosure V S.G1) ≤ S.G1)
    (hcomm : ⁅conjSub x (conjClosure S.V3 S.G1), conjClosure S.V3 S.G1⁆ =
      conjSub x (fsuV1 T V))
    (hA1 : fsuV1 T V ⊓ conjSub x (fsuV1 T V) = ⊥)
    {h : G} (hh : h ∈ S.G1) {t₀ t₁ : G} (ht₀ : t₀ ∈ S.V3) (ht₁ : t₁ ∈ S.V3)
    (hw₀ : x * h * t₀ * (x * h)⁻¹ ∉ pCoreOf 2 S.G1)
    (hw₁ : x * h * t₀ * (x * h)⁻¹ * t₁ * (x * h * t₀ * (x * h)⁻¹)⁻¹ * t₁⁻¹ ≠ 1) : False := by
  have hzV1 : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have hUab : IsElemAbelian 2 (conjClosure S.V3 S.G1) := hF.F911_3
  have hUN : ∀ k ∈ S.G1, ∀ u ∈ conjClosure S.V3 S.G1, k * u * k⁻¹ ∈ conjClosure S.V3 S.G1 :=
    fun k hk u hu =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hk) u).mp hu
  have hA2 : ∀ e ∈ conjSub x (fsuV1 T V), e = 1 ∨ e = x * S.z * x⁻¹ := by
    intro e he
    rcases S.mem_V1_iff.1 (mem_conjSub.mp he) with h1 | h1
    · left
      calc e = x * (x⁻¹ * e * x) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · right
      calc e = x * (x⁻¹ * e * x) * x⁻¹ := by group
        _ = x * S.z * x⁻¹ := by rw [h1]
  have hcommU : ∀ p ∈ conjSub x (conjClosure S.V3 S.G1), ∀ u ∈ conjClosure S.V3 S.G1,
      p * u * p⁻¹ * u⁻¹ ∈ conjSub x (fsuV1 T V) := by
    intro p hp u hu
    rw [← hcomm]
    have := Subgroup.commutator_mem_commutator hp hu
    rwa [commutatorElement_def] at this
  have hAU : conjSub x (fsuV1 T V) ≤ conjClosure S.V3 S.G1 := by
    rw [← hcomm, Subgroup.commutator_le]
    intro p hp u hu
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (hUN p (hXG hp) u hu) (Subgroup.inv_mem _ hu)
  have haA : x * S.z * x⁻¹ ∈ conjSub x (fsuV1 T V) := mul_mem_conjSub hzV1
  have haU := hAU haA
  have haV1 : x * S.z * x⁻¹ ∉ fsuV1 T V := by
    intro h1
    have h2 : x * S.z * x⁻¹ ∈ fsuV1 T V ⊓ conjSub x (fsuV1 T V) := ⟨h1, haA⟩
    rw [hA1, Subgroup.mem_bot] at h2
    apply S.z_ne_one
    calc S.z = x⁻¹ * (x * S.z * x⁻¹) * x := by group
      _ = 1 := by rw [h2]; group
  set c : Fin 6 → ZMod 2 :=
    ((Multiplicative.toAdd (β ⟨_, haU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    apply haV1
    refine (hβk ⟨_, haU⟩).1 ?_
    rw [← ofAdd_toAdd (β ⟨_, haU⟩)]
    have : Multiplicative.toAdd (β ⟨_, haU⟩) = 0 := Subtype.ext h0
    rw [this, ofAdd_zero]
  have hcoord : ∀ (p : G) (hp : p ∈ S.G1) (u : G) (hu : u ∈ conjClosure S.V3 S.G1),
      p * u * p⁻¹ * u⁻¹ ∈ conjSub x (fsuV1 T V) →
      vp (ρ ⟨p, hp⟩) ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) +
        ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = 0 ∨
      vp (ρ ⟨p, hp⟩) ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) +
        ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = c := by
    intro p hp u hu hpu
    have hpuU := hUN p hp u hu
    have he := hβe ⟨p, hp⟩ ⟨u, hu⟩ ⟨_, hpuU⟩ rfl
    have hv : vp (ρ ⟨p, hp⟩) ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2) = ((Multiplicative.toAdd (β ⟨_, hpuU⟩) : ↥(evenWeight 6)) :
          Fin 6 → ZMod 2) := by
      rw [he]
      rfl
    rw [hv]
    rcases hA2 _ hpu with h1 | h1
    · left
      have e : (⟨p * u * p⁻¹, hpuU⟩ : ↥(conjClosure S.V3 S.G1)) = ⟨u, hu⟩ := by
        apply Subtype.ext
        calc p * u * p⁻¹ = (p * u * p⁻¹ * u⁻¹) * u := by group
          _ = u := by rw [h1, one_mul]
      rw [e]
      exact vadd_self _
    · right
      have e : (⟨p * u * p⁻¹, hpuU⟩ : ↥(conjClosure S.V3 S.G1)) = ⟨_, haU⟩ * ⟨u, hu⟩ := by
        apply Subtype.ext
        show p * u * p⁻¹ = x * S.z * x⁻¹ * u
        rw [← h1]
        group
      rw [e, map_mul, toAdd_mul, AddSubgroup.coe_add, add_assoc, vadd_self, add_zero]
  have hwt : ∀ k l : Fin 6, k < l → ∃ (u : G) (hu : u ∈ conjClosure S.V3 S.G1),
      ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = wt2v k l := by
    intro k l hkl
    have hmem : wt2v k l ∈ evenWeight 6 := mem_ev_of_sum_zero (wt2v_facts.1 k l hkl)
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd ⟨wt2v k l, hmem⟩)
    exact ⟨u, u.2, by rw [hu]; rfl⟩
  have hTv : ∀ (p : G) (hp : p ∈ conjSub x (conjClosure S.V3 S.G1)),
      TvOn6 (ρ ⟨p, hXG hp⟩) c := by
    intro p hp k l hkl
    obtain ⟨u, hu, hβu⟩ := hwt k l hkl
    have := hcoord p (hXG hp) u hu (hcommU p hp u hu)
    rw [hβu] at this
    exact this
  have hw₀X : x * h * t₀ * (x * h)⁻¹ ∈ conjSub x (conjClosure S.V3 S.G1) := by
    have e : x * h * t₀ * (x * h)⁻¹ = x * (h * t₀ * h⁻¹) * x⁻¹ := by group
    rw [e]
    exact mul_mem_conjSub (mem_conjClosure hh ht₀)
  have hτ1 : ρ ⟨_, hXG hw₀X⟩ ≠ 1 := fun h1 => hw₀ ((hker _).1 h1)
  obtain ⟨k₀, l₀, hkl₀, hd₀⟩ := exists_dwt2_ne _ hτ1
  have hc₀ : dwt2 (ρ ⟨_, hXG hw₀X⟩) k₀ l₀ = c :=
    ((hTv _ hw₀X) k₀ l₀ hkl₀).resolve_left hd₀
  obtain ⟨i, j, hij, hτ, hcij⟩ := tv6_swap _ k₀ l₀ hkl₀ hd₀ (hc₀ ▸ hTv _ hw₀X)
  rw [hc₀] at hcij
  have hX2 : ∀ (p : G) (hp : p ∈ conjSub x (conjClosure S.V3 S.G1)),
      ρ ⟨p, hXG hp⟩ = 1 ∨ ρ ⟨p, hXG hp⟩ = swap i j := by
    intro p hp
    by_cases h1 : ρ ⟨p, hXG hp⟩ = 1
    · exact Or.inl h1
    right
    obtain ⟨k₁, l₁, hkl₁, hd₁⟩ := exists_dwt2_ne _ h1
    have hc₁ : dwt2 (ρ ⟨p, hXG hp⟩) k₁ l₁ = c := ((hTv _ hp) k₁ l₁ hkl₁).resolve_left hd₁
    obtain ⟨i', j', hij', hσ, hcij'⟩ := tv6_swap _ k₁ l₁ hkl₁ hd₁ (hc₁ ▸ hTv _ hp)
    rw [hc₁, hcij] at hcij'
    rw [hσ]
    exact (wt2v_facts.2.1 i j i' j' hij hij' hcij').symm
  have hVyG : conjSub (x * h) V ≤ S.G1 := by
    refine le_trans ?_ hVG
    rw [conjSub_mul]
    refine conjSub_mono _ fun v hv => ?_
    have h1 := mem_conjSub.mp hv
    have e : v = h * (h⁻¹ * v * h) * h⁻¹ := by group
    rw [e]
    exact mem_conjClosure hh h1
  have hVyVH : ∀ v ∈ conjSub (x * h) V, x⁻¹ * v * x ∈ conjClosure V S.G1 := by
    intro v hv
    have h1 := mem_conjSub.mp hv
    have e : x⁻¹ * v * x = h * ((x * h)⁻¹ * v * (x * h)) * h⁻¹ := by group
    rw [e]
    exact mem_conjClosure hh h1
  have hfixU : ∀ k l : Fin 6, k < l → wt2v k l i = wt2v k l j → ∀ (v : G)
      (hv : v ∈ conjSub (x * h) V), dwt2 (ρ ⟨v, hVyG hv⟩) k l = 0 ∨
        dwt2 (ρ ⟨v, hVyG hv⟩) k l = c := by
    intro k l hkl hfix v hv
    obtain ⟨u, hu, hβu⟩ := hwt k l hkl
    have hcent : ∀ p ∈ conjSub x (conjClosure S.V3 S.G1), p * u * p⁻¹ = u := by
      intro p hp
      have hpuU := hUN p (hXG hp) u hu
      have hβeq : β ⟨_, hpuU⟩ = β ⟨u, hu⟩ := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        have he := hβe ⟨p, hXG hp⟩ ⟨u, hu⟩ ⟨_, hpuU⟩ rfl
        rw [he]
        show vp (ρ ⟨p, hXG hp⟩) ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) :
          Fin 6 → ZMod 2) = ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) :
            Fin 6 → ZMod 2)
        rw [hβu]
        rcases hX2 p hp with h1 | h1 <;> rw [h1]
        · rfl
        · exact wt2v_facts.2.2 i j k l hfix
      have h1 : p * u * p⁻¹ * u⁻¹ ∈ fsuV1 T V := by
        have := (hβk (⟨_, hpuU⟩ * (⟨u, hu⟩ : ↥(conjClosure S.V3 S.G1))⁻¹)).1 (by
          rw [map_mul, map_inv, hβeq]
          exact mul_inv_cancel _)
        exact this
      have h2 : p * u * p⁻¹ * u⁻¹ ∈ fsuV1 T V ⊓ conjSub x (fsuV1 T V) :=
        ⟨h1, hcommU p hp u hu⟩
      rw [hA1, Subgroup.mem_bot] at h2
      calc p * u * p⁻¹ = (p * u * p⁻¹ * u⁻¹) * u := by group
        _ = u := by rw [h2, one_mul]
    have hxQ : x⁻¹ * u * x ∈ pCoreOf 2 S.G1 := by
      have := mem_conjSub.mp (hUQ hu)
      exact this
    have hxC : x⁻¹ * u * x ∈ Subgroup.centralizer (conjClosure S.V3 S.G1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u' hu'
      have h1 := hcent (x * u' * x⁻¹) (mul_mem_conjSub hu')
      calc u' * (x⁻¹ * u * x) = x⁻¹ * ((x * u' * x⁻¹) * u) * x := by group
        _ = x⁻¹ * ((x * u' * x⁻¹) * u * (x * u' * x⁻¹)⁻¹ * (x * u' * x⁻¹)) * x := by group
        _ = x⁻¹ * (u * (x * u' * x⁻¹)) * x := by rw [h1]
        _ = (x⁻¹ * u * x) * u' := by group
    have h3 := S.comm_VH_HC hNS h13315 h1356two hG1 hxQ hxC (hVyVH v hv)
    have h4 : v * u * v⁻¹ * u⁻¹ ∈ conjSub x (fsuV1 T V) := by
      rw [mem_conjSub]
      have e : x⁻¹ * (v * u * v⁻¹ * u⁻¹) * x = (x⁻¹ * v * x) * (x⁻¹ * u * x) *
          (x⁻¹ * v * x)⁻¹ * (x⁻¹ * u * x)⁻¹ := by group
      rw [e]
      exact h3
    have := hcoord v (hVyG hv) u hu h4
    rw [hβu] at this
    exact this
  have hVy2 : ∀ (v : G) (hv : v ∈ conjSub (x * h) V),
      ρ ⟨v, hVyG hv⟩ = 1 ∨ ρ ⟨v, hVyG hv⟩ = swap i j := by
    intro v hv
    refine tv6_axis i j hij _ fun k l hkl hfix => ?_
    rw [← hcij]
    exact hfixU k l hkl hfix v hv
  have hAy : conjSub (x * h) (fsuV1 T V) = conjSub x (fsuV1 T V) := by
    rw [conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hF.H_normalizes_V₁ hh)]
  have hV3yX : conjSub (x * h) S.V3 ≤ conjSub x (conjClosure S.V3 S.G1) := by
    rw [conjSub_mul]
    refine conjSub_mono _ fun t ht => ?_
    have h1 := mem_conjSub.mp ht
    have e : t = h * (h⁻¹ * t * h) * h⁻¹ := by group
    rw [e]
    exact mem_conjClosure hh h1
  have hV3N : S.V3 ≤ Subgroup.normalizer (conjSub (x * h) S.V3 : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun t ht t' ht' => ?_
    have h1 := hcommU t'⁻¹ ((conjSub x (conjClosure S.V3 S.G1)).inv_mem (hV3yX ht')) t
      (le_conjClosure S.V3 S.G1 ht)
    rw [← hAy] at h1
    have h2 : t'⁻¹ * t * t'⁻¹⁻¹ * t⁻¹ ∈ conjSub (x * h) S.V3 :=
      conjSub_mono _ (S.V1_le_V3) h1
    have e : t * t' * t⁻¹ = t' * (t'⁻¹ * t * t'⁻¹⁻¹ * t⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ht' h2
  have hyz : (x * h) * S.z * (x * h)⁻¹ = x * S.z * x⁻¹ := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (show h ∈ Subgroup.centralizer ({S.z} : Set G) from hh)
    calc (x * h) * S.z * (x * h)⁻¹ = x * (h * S.z) * h⁻¹ * x⁻¹ := by group
      _ = x * (S.z * h) * h⁻¹ * x⁻¹ := by rw [this]
      _ = x * S.z * x⁻¹ := by group
  have hnN : ∀ t ∈ S.V3, (x * h)⁻¹ * t * (x * h) ∈ Subgroup.normalizer (V : Set G) := by
    intro t ht
    refine S.G1_inf_G3_le h13315 (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · rw [G1, Subgroup.mem_centralizer_singleton_iff]
      have hta : t * (x * S.z * x⁻¹) = (x * S.z * x⁻¹) * t :=
        F7.isElemAbelian_comm hUab (le_conjClosure S.V3 S.G1 ht) haU
      rw [← hyz] at hta
      calc (x * h)⁻¹ * t * (x * h) * S.z =
          (x * h)⁻¹ * (t * ((x * h) * S.z * (x * h)⁻¹)) * (x * h) := by group
        _ = (x * h)⁻¹ * (((x * h) * S.z * (x * h)⁻¹) * t) * (x * h) := by rw [hta]
        _ = S.z * ((x * h)⁻¹ * t * (x * h)) := by group
    · have h1 := conjSub_le_normalizer (g := (x * h)⁻¹) hV3N
      rw [conjSub_conjSub_inv] at h1
      refine h1 ?_
      have := mul_mem_conjSub (g := (x * h)⁻¹) ht
      rwa [inv_inv] at this
  have hV3Vy : ∀ t ∈ S.V3, t ∈ Subgroup.normalizer (conjSub (x * h) V : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro e
    rw [mem_conjSub, mem_conjSub]
    have h1 := Subgroup.mem_normalizer_iff.mp (hnN t ht) ((x * h)⁻¹ * e * (x * h))
    have e' : (x * h)⁻¹ * (t * e * t⁻¹) * (x * h) = ((x * h)⁻¹ * t * (x * h)) *
        ((x * h)⁻¹ * e * (x * h)) * ((x * h)⁻¹ * t * (x * h))⁻¹ := by group
    rw [e']
    exact h1
  have hw₀Vy : x * h * t₀ * (x * h)⁻¹ ∈ conjSub (x * h) V := mul_mem_conjSub (S.V3_le_V ht₀)
  have hV1Vy : ∀ e ∈ fsuV1 T V, e ∈ conjSub (x * h) V → e = 1 := by
    intro e he heV
    by_contra he1
    have hez : e = S.z := (S.mem_V1_iff.1 he).resolve_left he1
    have hle : fsuV1 T V ≤ conjSub (x * h)⁻¹⁻¹ V := by
      rw [inv_inv]
      intro e' he'
      rcases S.mem_V1_iff.1 he' with h1 | h1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [h1, ← hez]
        exact heV
    have hbot := S.comm_conjSub_V_eq_bot hab hle
    rw [inv_inv] at hbot
    have h2 := Subgroup.commutator_mem_commutator (S.V3_le_V ht₁) hw₀Vy
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h2
    apply hw₁
    have e' : x * h * t₀ * (x * h)⁻¹ * t₁ * (x * h * t₀ * (x * h)⁻¹)⁻¹ * t₁⁻¹ =
        (t₁ * (x * h * t₀ * (x * h)⁻¹) * t₁⁻¹ * (x * h * t₀ * (x * h)⁻¹)⁻¹)⁻¹ := by group
    rw [e', h2, inv_one]
  have hQt : ∀ q ∈ conjSub (x * h) V, q ∈ pCoreOf 2 S.G1 → ∀ t ∈ S.V3, q * t * q⁻¹ = t := by
    intro q hq hqQ t ht
    have h1 : q * t * q⁻¹ * t⁻¹ ∈ fsuV1 T V := by
      rw [hF.toHypF91.pCoreOf_eq_centralizerMod] at hqQ
      exact hqQ.2.2 t (le_conjClosure S.V3 S.G1 ht)
    have h2 : q * t * q⁻¹ * t⁻¹ ∈ conjSub (x * h) V := by
      have h3 := (Subgroup.mem_normalizer_iff.mp (hV3Vy t ht) q⁻¹).mp (Subgroup.inv_mem _ hq)
      have e : q * t * q⁻¹ * t⁻¹ = q * (t * q⁻¹ * t⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hq h3
    have h4 := hV1Vy _ h1 h2
    calc q * t * q⁻¹ = (q * t * q⁻¹ * t⁻¹) * t := by group
      _ = t := by rw [h4, one_mul]
  have hE : ∀ v ∈ conjSub (x * h) V, ∀ t ∈ S.V3, v * t * v⁻¹ * t⁻¹ ∈ conjSub x (fsuV1 T V) := by
    intro v hv t ht
    rcases hVy2 v hv with h1 | h1
    · have hvQ := (hker _).1 h1
      rw [hQt v hv hvQ t ht, mul_inv_cancel]
      exact Subgroup.one_mem _
    · have hqG : (x * h * t₀ * (x * h)⁻¹)⁻¹ * v ∈ S.G1 :=
        S.G1.mul_mem (S.G1.inv_mem (hXG hw₀X)) (hVyG hv)
      have hqQ : (x * h * t₀ * (x * h)⁻¹)⁻¹ * v ∈ pCoreOf 2 S.G1 := by
        refine (hker ⟨_, hqG⟩).1 ?_
        have e : (⟨_, hqG⟩ : ↥S.G1) = (⟨_, hXG hw₀X⟩ : ↥S.G1)⁻¹ * ⟨v, hVyG hv⟩ := rfl
        rw [e, map_mul, map_inv, h1, hτ, inv_mul_cancel]
      have hqVy : (x * h * t₀ * (x * h)⁻¹)⁻¹ * v ∈ conjSub (x * h) V :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hw₀Vy) hv
      have h2 := hQt _ hqVy hqQ t ht
      have h3 := hcommU _ hw₀X t (le_conjClosure S.V3 S.G1 ht)
      have e : v * t * v⁻¹ * t⁻¹ = (x * h * t₀ * (x * h)⁻¹) *
          (((x * h * t₀ * (x * h)⁻¹)⁻¹ * v) * t * ((x * h * t₀ * (x * h)⁻¹)⁻¹ * v)⁻¹) *
            (x * h * t₀ * (x * h)⁻¹)⁻¹ * t⁻¹ := by group
      rw [e, h2]
      exact h3
  set w := (x * h)⁻¹ * t₁ * (x * h) with hwdef
  have hwN : w ∈ Subgroup.normalizer (V : Set G) := hnN t₁ ht₁
  have hwV : ∀ v ∈ V, w * v * w⁻¹ * v⁻¹ ∈ fsuV1 T V := by
    intro v hv
    have h1 := hE ((x * h) * v * (x * h)⁻¹) (mul_mem_conjSub hv) t₁ ht₁
    rw [← hAy, mem_conjSub] at h1
    have e : (x * h)⁻¹ * ((x * h) * v * (x * h)⁻¹ * t₁ * ((x * h) * v * (x * h)⁻¹)⁻¹ * t₁⁻¹) *
        (x * h) = (w * v * w⁻¹ * v⁻¹)⁻¹ := by rw [hwdef]; group
    rw [e] at h1
    have := (fsuV1 T V).inv_mem h1
    rwa [inv_inv] at this
  have hσ := fixMod_cases (S.frame.ρ ⟨w, hwN⟩) (by
    intro y' hy'
    set v : ↥V := S.frame.ψ.symm ⟨y', hy'⟩ with hvdef
    have h1 := S.psi_conj ⟨w, hwN⟩ v
    have hψv : S.frame.ψ v = ⟨y', hy'⟩ := by rw [hvdef, MulEquiv.apply_symm_apply]
    rw [hψv] at h1
    have h2 := hwV v v.2
    have hwv : (w : G) * v * w⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hwN v).mp v.2
    rcases S.mem_V1_iff.1 h2 with h3 | h3
    · left
      have e : (⟨(w : G) * v * w⁻¹, hwv⟩ : ↥V) = v := by
        apply Subtype.ext
        calc (w : G) * v * w⁻¹ = (w * (v : G) * w⁻¹ * (v : G)⁻¹) * (v : G) := by group
          _ = v := by rw [h3, one_mul]
      have h4 : ((S.frame.ψ ⟨(w : G) * v * w⁻¹, hwv⟩ : ↥W4) : P6) = y' := by
        rw [e, hψv]
      rw [show (⟨((⟨w, hwN⟩ : ↥(Subgroup.normalizer (V : Set G))) : G) * v *
          ((⟨w, hwN⟩ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹, _⟩ : ↥V) =
          ⟨(w : G) * v * w⁻¹, hwv⟩ from rfl] at h1
      show ((act4 (S.frame.ρ ⟨w, hwN⟩) ⟨y', hy'⟩ : ↥W4) : P6) * y'⁻¹ = 1
      rw [← h1, h4]
      exact mul_inv_cancel _
    · right
      have e : (⟨(w : G) * v * w⁻¹, hwv⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ * v := by
        apply Subtype.ext
        show (w : G) * v * w⁻¹ = S.z * v
        rw [← h3]
        group
      have h4 : ((S.frame.ψ ⟨(w : G) * v * w⁻¹, hwv⟩ : ↥W4) : P6) = e0123 * y' := by
        rw [e, map_mul, Subgroup.coe_mul, S.psi_z, hψv]
      rw [show (⟨((⟨w, hwN⟩ : ↥(Subgroup.normalizer (V : Set G))) : G) * v *
          ((⟨w, hwN⟩ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹, _⟩ : ↥V) =
          ⟨(w : G) * v * w⁻¹, hwv⟩ from rfl] at h1
      show ((act4 (S.frame.ρ ⟨w, hwN⟩) ⟨y', hy'⟩ : ↥W4) : P6) * y'⁻¹ = e0123
      rw [← h1, h4]
      exact mul_inv_cancel_right _ _)
  have hfix : FixW3 (S.frame.ρ ⟨w, hwN⟩) := by
    rcases hσ with h1 | h1 <;> rw [h1]
    · exact fixW3_one_swap45.1
    · exact fixW3_one_swap45.2
  have ht₀w : w * t₀ * w⁻¹ = t₀ := by
    have h1 := (S.conj_eq_iff ⟨w, hwN⟩ ⟨t₀, S.V3_le_V ht₀⟩).2
    refine h1 (Subtype.ext ?_)
    obtain ⟨hV, hW⟩ := S.mem_pre.1 ht₀
    rw [act4_coe]
    exact hfix _ ⟨(S.frame.ψ ⟨t₀, S.V3_le_V ht₀⟩).2, hW⟩
  apply hw₁
  rw [hwdef] at ht₀w
  have key : t₁ * (x * h * t₀ * (x * h)⁻¹) * t₁⁻¹ = x * h * t₀ * (x * h)⁻¹ := by
    calc t₁ * (x * h * t₀ * (x * h)⁻¹) * t₁⁻¹ = (x * h) * (((x * h)⁻¹ * t₁ * (x * h)) * t₀ *
        ((x * h)⁻¹ * t₁ * (x * h))⁻¹) * (x * h)⁻¹ := by group
      _ = x * h * t₀ * (x * h)⁻¹ := by rw [ht₀w]
  calc x * h * t₀ * (x * h)⁻¹ * t₁ * (x * h * t₀ * (x * h)⁻¹)⁻¹ * t₁⁻¹ =
      (x * h * t₀ * (x * h)⁻¹) * (t₁ * (x * h * t₀ * (x * h)⁻¹) * t₁⁻¹)⁻¹ := by group
    _ = 1 := by rw [key, mul_inv_cancel]

theorem false_caseB_cover (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz)
    (hab : IsMulCommutative ↥(conjClosure V S.G1)) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {ρ : ↥S.G1 →* Perm (Fin 6)} (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
    (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
    {x : G} (hUQ : conjClosure S.V3 S.G1 ≤ conjSub x (pCoreOf 2 S.G1))
    (hXQ : ¬ conjSub x (conjClosure S.V3 S.G1) ≤ pCoreOf 2 S.G1)
    (hXG : conjSub x (conjClosure S.V3 S.G1) ≤ S.G1)
    (hVG : conjSub x (conjClosure V S.G1) ≤ S.G1)
    (hcomm : ⁅conjSub x (conjClosure S.V3 S.G1), conjClosure S.V3 S.G1⁆ =
      conjSub x (fsuV1 T V))
    (hA1 : fsuV1 T V ⊓ conjSub x (fsuV1 T V) = ⊥) : False := by
  have hUab : IsElemAbelian 2 (conjClosure S.V3 S.G1) := hF.F911_3
  have hUN : ∀ k ∈ S.G1, ∀ u ∈ conjClosure S.V3 S.G1, k * u * k⁻¹ ∈ conjClosure S.V3 S.G1 :=
    fun k hk u hu =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hk) u).mp hu
  have hQN : ∀ k ∈ S.G1, ∀ q ∈ pCoreOf 2 S.G1, k * q * k⁻¹ ∈ pCoreOf 2 S.G1 :=
    fun k hk q hq => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 S.G1 hk) q).mp hq
  obtain ⟨h, hh, t₀, ht₀, hw₀⟩ : ∃ h ∈ S.G1, ∃ t₀ ∈ S.V3,
      x * h * t₀ * (x * h)⁻¹ ∉ pCoreOf 2 S.G1 := by
    by_contra hcon
    push Not at hcon
    apply hXQ
    rw [conjSub_le_iff]
    refine conjClosure_le fun k hk t ht => ?_
    rw [mem_conjSub, inv_inv]
    have e : x * (k * t * k⁻¹) * x⁻¹ = x * k * t * (x * k)⁻¹ := by group
    rw [e]
    exact hcon k hk t ht
  have hw₀X : x * h * t₀ * (x * h)⁻¹ ∈ conjSub x (conjClosure S.V3 S.G1) := by
    have e : x * h * t₀ * (x * h)⁻¹ = x * (h * t₀ * h⁻¹) * x⁻¹ := by group
    rw [e]
    exact mul_mem_conjSub (mem_conjClosure hh ht₀)
  set w₀ := x * h * t₀ * (x * h)⁻¹ with hw₀def
  have hw₀G := hXG hw₀X
  obtain ⟨k, hk, t, ht, hkt⟩ : ∃ k ∈ S.G1, ∃ t ∈ S.V3,
      w₀ * (k * t * k⁻¹) * w₀⁻¹ * (k * t * k⁻¹)⁻¹ ∉ fsuV1 T V := by
    by_contra hcon
    push Not at hcon
    apply hw₀
    rw [hF.toHypF91.pCoreOf_eq_centralizerMod]
    refine ⟨hw₀G, hF.H_normalizes_V₁ hw₀G, fun u hu => ?_⟩
    let S' : Subgroup G :=
      { carrier := {u | u ∈ conjClosure S.V3 S.G1 ∧ w₀ * u * w₀⁻¹ * u⁻¹ ∈ fsuV1 T V}
        mul_mem' := by
          rintro u₁ u₂ ⟨hu₁, h₁⟩ ⟨hu₂, h₂⟩
          refine ⟨Subgroup.mul_mem _ hu₁ hu₂, ?_⟩
          have hc : u₁ * (w₀ * u₂ * w₀⁻¹ * u₂⁻¹) = (w₀ * u₂ * w₀⁻¹ * u₂⁻¹) * u₁ :=
            F7.isElemAbelian_comm hUab hu₁ (Subgroup.mul_mem _ (hUN _ hw₀G _ hu₂)
              (Subgroup.inv_mem _ hu₂))
          have e : w₀ * (u₁ * u₂) * w₀⁻¹ * (u₁ * u₂)⁻¹ =
              (w₀ * u₁ * w₀⁻¹ * u₁⁻¹) * (u₁ * (w₀ * u₂ * w₀⁻¹ * u₂⁻¹) * u₁⁻¹) := by group
          rw [e, hc, mul_inv_cancel_right]
          exact Subgroup.mul_mem _ h₁ h₂
        one_mem' := ⟨Subgroup.one_mem _, by simp⟩
        inv_mem' := by
          rintro u ⟨hu, h₁⟩
          refine ⟨Subgroup.inv_mem _ hu, ?_⟩
          have hc : u * (w₀ * u * w₀⁻¹) = (w₀ * u * w₀⁻¹) * u :=
            F7.isElemAbelian_comm hUab hu (hUN _ hw₀G _ hu)
          have e : w₀ * u⁻¹ * w₀⁻¹ * u⁻¹⁻¹ = (w₀ * u * w₀⁻¹ * u⁻¹)⁻¹ := by
            calc w₀ * u⁻¹ * w₀⁻¹ * u⁻¹⁻¹ = (w₀ * u * w₀⁻¹)⁻¹ * u := by group
              _ = u * (u⁻¹ * (w₀ * u * w₀⁻¹)⁻¹ * u) := by group
              _ = u * (w₀ * u * w₀⁻¹)⁻¹ := by
                rw [show u⁻¹ * (w₀ * u * w₀⁻¹)⁻¹ * u = (u⁻¹ * (w₀ * u * w₀⁻¹) * u)⁻¹ by
                  group]
                rw [show u⁻¹ * (w₀ * u * w₀⁻¹) * u = w₀ * u * w₀⁻¹ by
                  rw [mul_assoc, ← hc]; group]
              _ = (w₀ * u * w₀⁻¹ * u⁻¹)⁻¹ := by
                rw [show (w₀ * u * w₀⁻¹ * u⁻¹)⁻¹ = u * (w₀ * u * w₀⁻¹)⁻¹ by group]
          rw [e]
          exact Subgroup.inv_mem _ h₁ }
    have hle : conjClosure S.V3 S.G1 ≤ S' := conjClosure_le fun k hk t ht =>
      ⟨mem_conjClosure hk ht, hcon k hk t ht⟩
    exact (hle hu).2
  have hk' : k⁻¹ ∈ S.G1 := S.G1.inv_mem hk
  have hUk : conjSub k⁻¹ (conjClosure S.V3 S.G1) = conjClosure S.V3 S.G1 :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 S.G1 hk')
  have hGk : conjSub k⁻¹ S.G1 = S.G1 := F7.conjSub_eq_of_mem_normalizer
    (Subgroup.le_normalizer hk')
  have hV1k : conjSub k⁻¹ (fsuV1 T V) = fsuV1 T V :=
    F7.conjSub_eq_of_mem_normalizer (hF.H_normalizes_V₁ hk')
  refine S.false_caseB_cover_core hNS h13315 h1356two hG1 hab hF hker hβs hβk hβe
    (x := k⁻¹ * x) ?_ ?_ ?_ ?_ ?_ hh ht₀ ht ?_ ?_
  · rw [conjSub_mul, ← hUk]
    exact conjSub_mono _ hUQ
  · rw [conjSub_mul]
    exact (conjSub_mono _ hXG).trans hGk.le
  · rw [conjSub_mul]
    exact (conjSub_mono _ hVG).trans hGk.le
  · rw [conjSub_mul, conjSub_mul]
    calc ⁅conjSub k⁻¹ (conjSub x (conjClosure S.V3 S.G1)), conjClosure S.V3 S.G1⁆
        = ⁅conjSub k⁻¹ (conjSub x (conjClosure S.V3 S.G1)),
            conjSub k⁻¹ (conjClosure S.V3 S.G1)⁆ := by rw [hUk]
      _ = conjSub k⁻¹ ⁅conjSub x (conjClosure S.V3 S.G1), conjClosure S.V3 S.G1⁆ :=
          conjSub_commutator _ _ _
      _ = conjSub k⁻¹ (conjSub x (fsuV1 T V)) := by rw [hcomm]
  · rw [conjSub_mul, ← hV1k, ← conjSub_inf, hV1k, hA1, conjSub_bot]
  · intro hQ
    apply hw₀
    have e : w₀ = k * ((k⁻¹ * x) * h * t₀ * ((k⁻¹ * x) * h)⁻¹) * k⁻¹ := by rw [hw₀def]; group
    rw [e]
    exact hQN k hk _ hQ
  · intro h1
    apply hkt
    have e : w₀ * (k * t * k⁻¹) * w₀⁻¹ * (k * t * k⁻¹)⁻¹ = k * ((k⁻¹ * x) * h * t₀ *
        ((k⁻¹ * x) * h)⁻¹ * t * ((k⁻¹ * x) * h * t₀ * ((k⁻¹ * x) * h)⁻¹)⁻¹ * t⁻¹) * k⁻¹ := by
      rw [hw₀def]; group
    rw [e, h1, mul_one, mul_inv_cancel]
    exact (fsuV1 T V).one_mem

end Setting4


theorem lem13827ThreeDD_holds (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) : Lem13827ThreeDD := by
  intro G _ _ T L V S hNS hNU hG1 hab hF hM γ γ' g s hcase
  obtain ⟨K, -, -, -, -, hcases⟩ := hM
  have key : ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
      F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) →
      ¬ F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) < conjClosure S.V3 S.G1 := by
    intro γ γ' g s hDγ hDH
    obtain ⟨hUQ, hXQ, hXG, hcomm⟩ := S.caseB_data hF s hDγ hDH
    obtain ⟨ha, haV⟩ := S.caseB_a hF s hXG hcomm
    rcases hcases with ⟨-, ρ, hker, -, honto, ⟨β, -, hβk, hβe⟩ | ⟨β, hβs, hβk, hβe⟩⟩ |
      ⟨-, ρ, hρs, -, β, -, hβk, hβe⟩
    · obtain ⟨h, hh, hb, hb1⟩ := S.exists_conj_V2_nat honto hβk hβe ha haV
      exact S.false_of_swap hUQ hXQ hh hb hb1
    · have hstab : stab γ = conjSub (g : G) S.G1 := by
        rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
      have hVG : conjSub (g : G)⁻¹ (conjClosure V S.G1) ≤ S.G1 := by
        rw [conjSub_le_iff, inv_inv, ← hstab]
        exact (hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans inf_le_right)
      have hA1 : fsuV1 T V ⊓ conjSub (g : G)⁻¹ (fsuV1 T V) = ⊥ := by
        have := congrArg (conjSub (g : G)⁻¹) (hF.F913_5b s)
        rwa [conjSub_inf, F8.A₁, conjSub_conjSub_inv, conjSub_bot, inf_comm] at this
      exact S.false_caseB_cover hNS h13315 h1356two hG1 hab hF hker hβs hβk hβe hUQ hXQ hXG
        hVG hcomm hA1
    · obtain ⟨h, hh, hb, hb1⟩ := S.exists_conj_V2_hat hρs hβk hβe ha haV
      exact S.false_of_swap hUQ hXQ hh hb hb1
  rcases hcase with hDγ | hDH
  · refine ⟨?_, hDγ⟩
    by_contra hne
    exact key γ γ' g s hDγ (lt_of_le_of_ne (centralizerMod_le_left _ _ _) hne)
  · refine ⟨hDH, ?_⟩
    by_contra hne
    have hlt : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) < F8.Uγ S.V3 S.G1 (g : G) :=
      lt_of_le_of_ne (centralizerMod_le_left _ _ _) hne
    obtain ⟨δ, δ', k, y, sk, -, -, hUk, hUy, hDHk, hDγk⟩ :=
      hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s hlt)
    refine key δ δ' k sk (by rw [hDγk, hDH, hUk]) ?_
    rw [hDHk, ← hUy]
    refine lt_of_le_of_ne (conjSub_mono _ hlt.le) fun he => hlt.ne ?_
    have := congrArg (conjSub (y : G)⁻¹) he
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

theorem input13827Six_of_ident (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hId : Ident13827) : Input13827Six :=
  input13827Six_of h13315 h1356two hId (lem13827ThreeDD_holds h13315 h1356two)

end CFSG.Quasithin.H13.A6
