module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.CGT.PushingUpLit.SYMB.Delta5Fix
public import CFSG.CGT.PushingUpLit.SYMB.Split5
public import CFSG.CGT.PushingUpLit.SYMB.Coho5
public import CFSG.GroupTheory.CoprimeSectionStability

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement
open CFSG.ComponentClassification.AschbacherTheorem3 (centerOf frattiniOf)

variable {G : Type} [Group G] [Finite G]

private theorem three_subgroups_mem_k334 {N H₁ H₂ H₃ : Subgroup G}
    (hn₁ : H₁ ≤ Subgroup.normalizer (N : Set G)) (hn₂ : H₂ ≤ Subgroup.normalizer (N : Set G))
    (hn₃ : H₃ ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N)
    (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) {x y z : G} (hx : x ∈ H₁) (hy : y ∈ H₂) (hz : z ∈ H₃) :
    ⁅⁅x, y⁆, z⁆ ∈ N := by
  have hconj : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have hu : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ ∈ N := by
    rw [← commutatorElement_inv]
    exact N.inv_mem (h2 (Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (H₃.inv_mem hz) (H₁.inv_mem hx)) hy))
  have hv : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ ∈ N := by
    rw [← commutatorElement_inv]
    exact N.inv_mem (h1 (Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (H₂.inv_mem hy) hz) (H₁.inv_mem hx)))
  have hxz := mul_mem (hn₁ hx) (hn₃ hz)
  have hxy := mul_mem (hn₁ hx) (hn₂ hy)
  have e1 : ⁅⁅x, y⁆, z⁆ = (x * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ * (x * y)⁻¹) *
      (x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ * (x * z)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact mul_mem (hconj _ hxy _ hv) (hconj _ hxz _ hu)

private theorem three_subgroups_le_k334 {N H₁ H₂ H₃ : Subgroup G}
    (hn₁ : H₁ ≤ Subgroup.normalizer (N : Set G)) (hn₂ : H₂ ≤ Subgroup.normalizer (N : Set G))
    (hn₃ : H₃ ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N)
    (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have hconj : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have key : ∀ w ∈ ⁅H₁, H₂⁆, w ∈ Subgroup.normalizer (N : Set G) ∧ ∀ z ∈ H₃, ⁅w, z⁆ ∈ N := by
    intro w hw
    have hw' : w ∈ Subgroup.closure {g : G | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g} := hw
    clear hw
    induction hw' using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hw
      refine ⟨?_, fun z hz => three_subgroups_mem_k334 hn₁ hn₂ hn₃ h1 h2 hx hy hz⟩
      have hxN := hn₁ hx
      have hyN := hn₂ hy
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
    | one => exact ⟨one_mem _, fun z _ => by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨mul_mem iha.1 ihb.1, fun z hz => ?_⟩
      have e1 : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (hconj _ iha.1 _ (ihb.2 z hz)) (iha.2 z hz)
    | inv a _ iha =>
      refine ⟨inv_mem iha.1, fun z hz => ?_⟩
      have e1 : ⁅a⁻¹, z⁆ = a⁻¹ * (⁅a, z⁆)⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      have := hconj _ (inv_mem iha.1) _ (N.inv_mem (iha.2 z hz))
      simpa using this
  exact Subgroup.commutator_le.mpr fun w hw z hz => (key w hw).2 z hz

private theorem mem_normalizer_commutator_k334 {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hX,
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hY]

private theorem commutator_le_left_of_le_normalizer_k334 {X Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (X : Set G)) : ⁅X, Y⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [show ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) by rw [commutatorElement_def]; group]
  exact X.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hY hy) x⁻¹).mp (X.inv_mem hx))

private theorem commutator_eq_commutator_commutator_k334 {A L : Subgroup G}
    (hL : ⁅L, L⁆ = L) (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ⁅A, L⁆ = ⁅⁅A, L⁆, L⁆ := by
  set W := ⁅⁅A, L⁆, L⁆ with hW
  refine le_antisymm ?_ ?_
  · have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
      mem_normalizer_commutator_k334
        (mem_normalizer_commutator_k334 (Subgroup.le_normalizer ha) (hAL ha)) (hAL ha)
    have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
      mem_normalizer_commutator_k334 (Subgroup.normalizer_commutator_ge_right A L hl)
        (Subgroup.le_normalizer hl)
    have h1 : ⁅⁅L, A⁆, L⁆ ≤ W := by rw [Subgroup.commutator_comm L A]
    have h3 := three_subgroups_le_k334 (N := W) (H₁ := L) (H₂ := L) (H₃ := A) hLW hLW hAW h1
      le_rfl
    rw [hL, Subgroup.commutator_comm L A] at h3
    exact h3
  · exact commutator_le_left_of_le_normalizer_k334 (Subgroup.normalizer_commutator_ge_right A L)

private theorem comm_le_inf_k334 {D Q : Subgroup G}
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hQN : Q ≤ Subgroup.normalizer (D : Set G)) :
    ⁅Q, D⁆ ≤ D ⊓ Q :=
  le_inf
    ((le_of_eq (Subgroup.commutator_comm Q D)).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left (H := Q) (K := D)).1 hQN))
    ((le_of_eq (Subgroup.commutator_comm Q D)).trans
      ((Subgroup.le_normalizer_iff_commutator_le_right (H := D) (K := Q)).1 hDQ))

private theorem comm_comm_N₁_k334 {D Q N₀ N₁ : Subgroup G} (h01 : N₁ ≤ N₀)
    (hD1 : ⁅D, N₁⁆ = ⊥) (hN0Q : ⁅N₀, Q⁆ ≤ N₁) : ⁅⁅Q, D⁆, N₁⁆ = ⊥ := by
  have hN1Q : ⁅N₁, Q⁆ ≤ N₁ := (Subgroup.commutator_mono h01 le_rfl).trans hN0Q
  refine Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Q) (H₂ := D) (H₃ := N₁) ?_ ?_
  · rw [hD1, Subgroup.commutator_bot_left]
  · rw [eq_bot_iff]
    calc ⁅⁅N₁, Q⁆, D⁆ ≤ ⁅N₁, D⁆ := Subgroup.commutator_mono hN1Q le_rfl
      _ = ⊥ := by rw [Subgroup.commutator_comm, hD1]

private theorem comm_N₀_D_sup_N₁_k334 {D N₀ N₁ : Subgroup G} (h01 : N₁ ≤ N₀)
    (hD0 : D ≤ Subgroup.normalizer (N₀ : Set G)) (hnat : NatA5Sec D N₀ N₁) :
    ⁅N₀, D⁆ ⊔ N₁ = N₀ := by
  obtain ⟨φ, ψ, hφs, hψs, hψk, hψeq⟩ := hnat
  have hSle : ⁅N₀, D⁆ ≤ N₀ := commutator_le_left_of_le_normalizer_k334 hD0
  let S' : Subgroup ↥N₀ := (⁅N₀, D⁆).subgroupOf N₀
  let T : Subgroup ↥(CFSG.Quasithin.G6.coreMod 5) := S'.map ψ
  have hT : ∀ w : ↥(CFSG.Quasithin.G6.coreMod 5), w ∈ T := by
    intro w
    refine (Subgroup.closure_le T).2 ?_ (CFSG.CGT.PushingUpLit.SYMB.Delta5Fix.comm_closure w)
    rintro x ⟨σ, u, hσ, rfl⟩
    have hσA : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hσ
    obtain ⟨d, hd⟩ := hφs ⟨σ, hσA⟩
    obtain ⟨n, hn⟩ := hψs u
    have hdval : (φ d : Equiv.Perm (Fin 5)) = σ := congrArg Subtype.val hd
    have hconj : (d : G) * (n : G) * (d : G)⁻¹ ∈ N₀ :=
      (Subgroup.mem_normalizer_iff.mp (hD0 d.2) (n : G)).mp n.2
    let n' : ↥N₀ := ⟨(d : G) * (n : G) * (d : G)⁻¹, hconj⟩
    have hψn' := hψeq d n n' rfl
    have hmem : ⁅(d : G), (n : G)⁆ ∈ ⁅N₀, D⁆ := by
      rw [Subgroup.commutator_comm N₀ D]
      exact Subgroup.commutator_mem_commutator d.2 n.2
    let s : ↥N₀ := ⟨⁅(d : G), (n : G)⁆, hSle hmem⟩
    have hs_mem : s ∈ S' := Subgroup.mem_subgroupOf.mpr hmem
    have hs_eq : s = n' * n⁻¹ := by
      apply Subtype.ext
      simp only [s, n', Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, mul_assoc]
    have hψs_eq : ψ s = CFSG.Quasithin.G6.coreAct 5 σ u * u⁻¹ := by
      rw [hs_eq, map_mul, map_inv, hψn', hn, hdval]
    exact Subgroup.mem_map.mpr ⟨s, hs_mem, hψs_eq⟩
  refine le_antisymm (sup_le hSle h01) ?_
  intro g hg
  obtain ⟨s, hs, hψs⟩ := Subgroup.mem_map.mp (hT (ψ ⟨g, hg⟩))
  have hsD : (s : G) ∈ ⁅N₀, D⁆ := Subgroup.mem_subgroupOf.mp hs
  have hker : (⟨g, hg⟩ : ↥N₀) * s⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψs]
    exact mul_inv_cancel _
  rw [hψk, Subgroup.mem_subgroupOf] at hker
  have hprod : (↑((⟨g, hg⟩ : ↥N₀) * s⁻¹) : G) * (s : G) = g := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have : (↑((⟨g, hg⟩ : ↥N₀) * s⁻¹) : G) * (s : G) ∈ N₁ ⊔ ⁅N₀, D⁆ :=
    Subgroup.mul_mem_sup hker hsD
  rw [hprod] at this
  simpa [sup_comm] using this

private theorem comm_S_sup_N₁_k334 {D Q N₀ N₁ : Subgroup G} (h01 : N₁ ≤ N₀)
    (h0Q : N₀ ≤ Q) (hD0 : D ≤ Subgroup.normalizer (N₀ : Set G)) (hQD : ⁅Q, D⁆ ≤ N₀)
    (hnat : NatA5Sec D N₀ N₁) : ⁅Q, D⁆ ⊔ N₁ = N₀ := by
  have hND : ⁅N₀, D⁆ ⊔ N₁ = N₀ := comm_N₀_D_sup_N₁_k334 h01 hD0 hnat
  have hle : ⁅N₀, D⁆ ≤ ⁅Q, D⁆ := Subgroup.commutator_mono h0Q le_rfl
  refine le_antisymm (sup_le hQD h01) ?_
  rw [← hND]
  exact sup_le_sup_right hle N₁

private theorem sq_mem_N₁_k334 {D N₀ N₁ : Subgroup G} (hnat : NatA5Sec D N₀ N₁) {x : G}
    (hx : x ∈ N₀) : x ^ 2 ∈ N₁ := by
  obtain ⟨φ, ψ, hφs, hψs, hψk, hψeq⟩ := hnat
  have h2 : ((⟨x, hx⟩ : ↥N₀) ^ 2) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_two]
    exact CFSG.CGT.PushingUpLit.SYMB.Split5.core_sq _
  rw [hψk, Subgroup.mem_subgroupOf] at h2
  simpa using h2

private theorem frattini_le_S_inter_N₁_k334 {D Q N₀ N₁ : Subgroup G} (hQ : IsPGroup 2 Q)
    (hN0Q : ⁅N₀, Q⁆ ≤ N₁) (hSN0 : ⁅Q, D⁆ ≤ N₀) (hSQ : ⁅Q, D⁆ ≤ Q)
    (hsq : ∀ x ∈ N₀, x ^ 2 ∈ N₁) : frattiniOf ⁅Q, D⁆ ≤ ⁅Q, D⁆ ⊓ N₁ := by
  set S := ⁅Q, D⁆ with hS
  haveI : Fact (IsPGroup 2 ↥S) := ⟨hQ.to_le hSQ⟩
  have hSS : ⁅S, S⁆ ≤ N₁ := (Subgroup.commutator_mono hSN0 hSQ).trans hN0Q
  have hfr : frattini S ≤ N₁.comap S.subtype := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥S) (p := 2)]
    refine (Subgroup.closure_le (N₁.comap S.subtype)).2 ?_
    rintro x (hx | ⟨y, rfl⟩)
    · have hcomm_le : _root_.commutator (↥S) ≤ N₁.subgroupOf S := by
        rw [_root_.commutator, Subgroup.commutator_le]
        intro a _ b _
        rw [Subgroup.mem_subgroupOf]
        change (S.subtype ⁅a, b⁆ : G) ∈ N₁
        rw [map_commutatorElement]
        exact hSS (Subgroup.commutator_mem_commutator a.2 b.2)
      exact Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mp (hcomm_le hx))
    · exact Subgroup.mem_comap.mpr (by simpa using hsq (y : G) (hSN0 y.2))
  rw [frattiniOf]
  refine le_inf ?_ (Subgroup.map_le_iff_le_comap.mpr hfr)
  rintro x ⟨y, hy, rfl⟩
  exact y.2

private theorem comm_S_eq_self_k334 {D Q : Subgroup G} (hperf : ⁅D, D⁆ = D)
    (hQN : Q ≤ Subgroup.normalizer (D : Set G)) : ⁅⁅Q, D⁆, D⁆ = ⁅Q, D⁆ :=
  (commutator_eq_commutator_commutator_k334 hperf hQN).symm

private theorem comm_S_S_le_frattini_k334 {D Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hSQ : ⁅Q, D⁆ ≤ Q) : ⁅⁅Q, D⁆, ⁅Q, D⁆⁆ ≤ frattiniOf ⁅Q, D⁆ := by
  set S := ⁅Q, D⁆ with hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : _root_.commutator (↥S) ≤ frattini ↥S :=
    CFSG.OrderReductions.FrattiniElementary.commutator_le_frattini 2 (hQ.to_le hSQ)
  have hmap : (_root_.commutator (↥S)).map S.subtype = ⁅S, S⁆ :=
    Subgroup.map_subtype_commutator S
  rw [frattiniOf, ← hmap]
  exact Subgroup.map_mono hcomm

private theorem comm_S_R_le_frattini_k334 {D Q N₀ N₁ : Subgroup G} (hQ : IsPGroup 2 Q)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hQN : Q ≤ Subgroup.normalizer (D : Set G))
    (hperf : ⁅D, D⁆ = D) (hSN0 : ⁅Q, D⁆ ≤ N₀) (hN0Q : ⁅N₀, Q⁆ ≤ N₁)
    (hD1 : ⁅D, N₁⁆ = ⊥) : ⁅⁅Q, D⁆, D ⊓ Q⁆ ≤ frattiniOf ⁅Q, D⁆ := by
  set S := ⁅Q, D⁆ with hS
  set R := D ⊓ Q with hR
  have hSQ : S ≤ Q := (comm_le_inf_k334 hDQ hQN).trans inf_le_right
  have hSS_le : ⁅S, S⁆ ≤ frattiniOf S := comm_S_S_le_frattini_k334 hQ hSQ
  have hSDQ : S ≤ Q ⊔ D := le_sup_of_le_left hSQ
  have hSN : Q ⊔ D ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSDQ).mp
      (inferInstance : (S.subgroupOf (Q ⊔ D)).Normal)
  have hDN : D ≤ Subgroup.normalizer (S : Set G) := le_trans le_sup_right hSN
  have hQNS : Q ≤ Subgroup.normalizer (S : Set G) := le_trans le_sup_left hSN
  have hRN : R ≤ Subgroup.normalizer (S : Set G) := le_trans inf_le_right hQNS
  have hSSN : Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((⁅S, S⁆ : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_commutator_k334 hg hg
  have hSR_S1 : ⁅S, R⁆ ≤ N₁ :=
    ((Subgroup.commutator_mono le_rfl inf_le_right).trans
      (Subgroup.commutator_mono hSN0 le_rfl)).trans hN0Q
  have h1 : ⁅⁅S, R⁆, D⁆ ≤ ⁅S, S⁆ := by
    calc ⁅⁅S, R⁆, D⁆ ≤ ⁅N₁, D⁆ := Subgroup.commutator_mono hSR_S1 le_rfl
      _ = ⊥ := by rw [Subgroup.commutator_comm, hD1]
      _ ≤ ⁅S, S⁆ := bot_le
  have h2 : ⁅⁅R, D⁆, S⁆ ≤ ⁅S, S⁆ :=
    Subgroup.commutator_mono
      ((Subgroup.commutator_mono inf_le_right le_rfl) : ⁅R, D⁆ ≤ S) le_rfl
  have hmain := three_subgroups_le_k334 (N := ⁅S, S⁆) (H₁ := D) (H₂ := S) (H₃ := R)
    (fun g hg => hSSN (hDN hg)) (fun g hg => hSSN (Subgroup.le_normalizer hg))
    (fun g hg => hSSN (hRN hg)) h1 h2
  have hDS : ⁅D, S⁆ = S := by
    rw [Subgroup.commutator_comm D S]
    exact comm_S_eq_self_k334 hperf hQN
  have hSR_SS : ⁅S, R⁆ ≤ ⁅S, S⁆ := by
    have := hmain
    rwa [hDS] at this
  exact hSR_SS.trans hSS_le

private theorem commutator_le_right_of_le_normalizer_k334 {X Y : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (Y : Set G)) : ⁅X, Y⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [show ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ by rw [commutatorElement_def]]
  exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hX hx) y).mp hy) (Y.inv_mem hy)

private theorem monoidHom_eq_one_of_comm_gen_k334 {S D : Subgroup G} {B : Type*} [Group B]
    (hDN : D ≤ Subgroup.normalizer (S : Set G)) (hDS : ⁅D, S⁆ = S) (f : ↥S →* B)
    (hfix : ∀ (d : ↥D) (x : ↥S) (hx' : (d : G) * (x : G) * (d : G)⁻¹ ∈ S),
      f ⟨(d : G) * (x : G) * (d : G)⁻¹, hx'⟩ = f x) :
    ∀ x : ↥S, f x = 1 := by
  have hgen' : ⁅D, S⁆ ≤ (f.ker).map S.subtype := by
    refine Subgroup.commutator_le.mpr fun d hd s hs => ?_
    have hmem : ⁅d, s⁆ ∈ S :=
      commutator_le_right_of_le_normalizer_k334 hDN
        (Subgroup.commutator_mem_commutator hd hs)
    refine Subgroup.mem_map.mpr ⟨⟨⁅d, s⁆, hmem⟩, ?_, rfl⟩
    have hprod : (⟨⁅d, s⁆, hmem⟩ : ↥S) =
        ⟨d * (s : G) * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDN hd) s).mp hs⟩ *
          (⟨s, hs⟩ : ↥S)⁻¹ := by
      apply Subtype.ext
      simp [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    rw [MonoidHom.mem_ker, hprod, map_mul, map_inv,
      hfix ⟨d, hd⟩ ⟨s, hs⟩ ((Subgroup.mem_normalizer_iff.mp (hDN hd) s).mp hs)]
    exact mul_inv_cancel _
  have hgen : S ≤ (f.ker).map S.subtype := (le_of_eq hDS.symm).trans hgen'
  intro x
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp (hgen x.2)
  have hyx : y = x := Subtype.ext hxy
  rw [← hyx]
  exact MonoidHom.mem_ker.mp hy

private theorem S_inter_N₁_le_centerOf_k334 {D Q N₀ N₁ : Subgroup G}
    (hN0Q : ⁅N₀, Q⁆ ≤ N₁) (hSN0 : ⁅Q, D⁆ ≤ N₀) (hSN₁ : ⁅⁅Q, D⁆, N₁⁆ = ⊥) :
    ⁅Q, D⁆ ⊓ N₁ ≤ centerOf ⁅Q, D⁆ := by
  set S := ⁅Q, D⁆ with hS
  have h : ⁅S ⊓ N₁, S⁆ = ⊥ := by
    rw [eq_bot_iff]
    calc ⁅S ⊓ N₁, S⁆ ≤ ⁅N₁, S⁆ := Subgroup.commutator_mono inf_le_right le_rfl
      _ = ⊥ := by rw [Subgroup.commutator_comm, hSN₁]
  have hc : S ⊓ N₁ ≤ Subgroup.centralizer (S : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  rw [centerOf]
  exact le_inf inf_le_left hc

private theorem exists_commHom_k334 {S P N₁ : Subgroup G} (hSP_le : ⁅S, P⁆ ≤ S ⊓ N₁)
    (hS1_cent : S ⊓ N₁ ≤ centerOf S) (p : ↥P) :
    ∃ c : ↥S →* ↥S, ∀ y : ↥S, (c y : G) = ⁅(y : G), (p : G)⁆ := by
  let c : ↥S →* ↥S :=
    { toFun := fun y =>
        ⟨⁅(y : G), (p : G)⁆, (hSP_le (Subgroup.commutator_mem_commutator y.2 p.2)).1⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y z => by
        apply Subtype.ext
        show ⁅(y : G) * (z : G), (p : G)⁆ = ⁅(y : G), (p : G)⁆ * ⁅(z : G), (p : G)⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hmemz : ⁅(z : G), (p : G)⁆ ∈ S ⊓ N₁ :=
          hSP_le (Subgroup.commutator_mem_commutator z.2 p.2)
        have hmemx : ⁅(y : G), (p : G)⁆ ∈ S ⊓ N₁ :=
          hSP_le (Subgroup.commutator_mem_commutator y.2 p.2)
        have hcy : (y : G) * ⁅(z : G), (p : G)⁆ * (y : G)⁻¹ = ⁅(z : G), (p : G)⁆ := by
          have := Subgroup.mem_centralizer_iff.mp (hS1_cent hmemz).2 (y : G) y.2
          rw [this]; group
        rw [hcy]
        exact (Subgroup.mem_centralizer_iff.mp (hS1_cent hmemx).2 ⁅(z : G), (p : G)⁆ hmemz.1) }
  exact ⟨c, fun y => rfl⟩

private theorem commHom_conj_k334 {D S P N₁ : Subgroup G}
    (hPcent : P ≤ Subgroup.centralizer (D : Set G))
    (hDcent : D ≤ Subgroup.centralizer (N₁ : Set G)) (hSP_le : ⁅S, P⁆ ≤ S ⊓ N₁)
    {p : ↥P} {c : ↥S →* ↥S} (hc : ∀ y : ↥S, (c y : G) = ⁅(y : G), (p : G)⁆)
    (d : ↥D) (y : ↥S) (hy' : (d : G) * (y : G) * (d : G)⁻¹ ∈ S) :
    c ⟨(d : G) * (y : G) * (d : G)⁻¹, hy'⟩ = c y := by
  apply Subtype.ext
  rw [hc, hc]
  have h1 : (d : G)⁻¹ * (p : G) * (d : G) = (p : G) := by
    have := Subgroup.mem_centralizer_iff.mp (hPcent p.2) (d : G) d.2
    calc (d : G)⁻¹ * (p : G) * (d : G) = (d : G)⁻¹ * ((p : G) * (d : G)) := by group
      _ = (d : G)⁻¹ * ((d : G) * (p : G)) := by rw [← this]
      _ = (p : G) := by group
  have h2 : ⁅(d : G) * (y : G) * (d : G)⁻¹, (p : G)⁆ =
      (d : G) * ⁅(y : G), (p : G)⁆ * (d : G)⁻¹ := by
    have hconj := conjugate_commutatorElement (g₃ := (d : G)) (g₁ := (y : G))
      (g₂ := (d : G)⁻¹ * (p : G) * (d : G))
    rw [show (d : G) * ((d : G)⁻¹ * (p : G) * (d : G)) * (d : G)⁻¹ = (p : G) by group] at hconj
    exact hconj.symm.trans (by rw [h1])
  rw [h2]
  have hmem : ⁅(y : G), (p : G)⁆ ∈ S ⊓ N₁ :=
    hSP_le (Subgroup.commutator_mem_commutator y.2 p.2)
  have hfix := Subgroup.mem_centralizer_iff.mp (hDcent d.2) ⁅(y : G), (p : G)⁆ hmem.2
  rw [← hfix]; group

private theorem comm_S_centralizer_D_k334 {D Q N₀ N₁ : Subgroup G}
    (hQ : IsPGroup 2 Q) (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hQN : Q ≤ Subgroup.normalizer (D : Set G)) (hperf : ⁅D, D⁆ = D)
    (h01 : N₁ ≤ N₀) (hSN0 : ⁅Q, D⁆ ≤ N₀) (hN0Q : ⁅N₀, Q⁆ ≤ N₁) (hD1 : ⁅D, N₁⁆ = ⊥) :
    ⁅⁅Q, D⁆, Q ⊓ Subgroup.centralizer (D : Set G)⁆ = ⊥ := by
  set S := ⁅Q, D⁆ with hS
  set P := Q ⊓ Subgroup.centralizer (D : Set G) with hP
  have hSQ : S ≤ Q := (comm_le_inf_k334 hDQ hQN).trans inf_le_right
  have hSDQ : S ≤ Q ⊔ D := le_sup_of_le_left hSQ
  have hSN : Q ⊔ D ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSDQ).mp
      (inferInstance : (S.subgroupOf (Q ⊔ D)).Normal)
  have hPN : P ≤ Subgroup.normalizer (S : Set G) :=
    (le_trans inf_le_left le_sup_left).trans hSN
  have hDN : D ≤ Subgroup.normalizer (S : Set G) := le_trans le_sup_right hSN
  have hDcent : D ≤ Subgroup.centralizer (N₁ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hD1
  have hSN₁ : ⁅S, N₁⁆ = ⊥ := comm_comm_N₁_k334 h01 hD1 hN0Q
  have hS1_cent : S ⊓ N₁ ≤ centerOf S := S_inter_N₁_le_centerOf_k334 hN0Q hSN0 hSN₁
  have hSP_le : ⁅S, P⁆ ≤ S ⊓ N₁ :=
    le_inf (commutator_le_left_of_le_normalizer_k334 hPN)
      ((Subgroup.commutator_mono le_rfl inf_le_left).trans
        ((Subgroup.commutator_mono hSN0 le_rfl).trans hN0Q))
  have hDS : ⁅D, S⁆ = S := by
    rw [Subgroup.commutator_comm D S]
    exact comm_S_eq_self_k334 hperf hQN
  have key : ∀ p ∈ P, ∀ x ∈ S, ⁅x, p⁆ = 1 := by
    intro p hp x hx
    obtain ⟨c, hc⟩ := exists_commHom_k334 hSP_le hS1_cent ⟨p, hp⟩
    have hc_one : ∀ y : ↥S, c y = 1 :=
      monoidHom_eq_one_of_comm_gen_k334 hDN hDS c
        (fun d y hy' => commHom_conj_k334 inf_le_right hDcent hSP_le hc d y hy')
    have h1 : ((c ⟨x, hx⟩ : ↥S) : G) = ((1 : ↥S) : G) :=
      congrArg Subtype.val (hc_one ⟨x, hx⟩)
    rw [hc ⟨x, hx⟩] at h1
    simpa using h1
  refine le_bot_iff.mp ?_
  exact Subgroup.commutator_le.mpr fun s hs p hp => Subgroup.mem_bot.mpr (key p hp s hs)

private theorem ker_le_pCoreOf_k334 {D : Subgroup G} (hD5 : IsAlt (Bar2 D) 5)
    {φ : ↥D →* alternatingGroup (Fin 5)} (hφs : Function.Surjective φ) {x : ↥D}
    (hx : φ x = 1) : (x : G) ∈ CFSG.Open.pCoreOf 2 D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup ↥D := CFSG.pCore 2 ↥D
  have hP : IsPGroup 2 P := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥D) 2
  obtain ⟨e⟩ := hD5
  have hPidx : P.index = 60 := by
    rw [Subgroup.index_eq_card]
    show Nat.card (↥D ⧸ CFSG.pCore 2 ↥D) = 60
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num
  have hKidx : φ.ker.index = 60 := by
    rw [Subgroup.index_eq_card]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num
  have hcard : Nat.card φ.ker = Nat.card P := by
    have h1 := φ.ker.card_mul_index
    have h2 := P.card_mul_index
    rw [hKidx] at h1
    rw [hPidx] at h2
    omega
  have hKp : IsPGroup 2 φ.ker := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    exact IsPGroup.of_card (n := n) (by rw [hcard, hn])
  have hKle : φ.ker ≤ P := CFSG.LieType.BorelTits.le_pCore 2 inferInstance hKp
  exact Subgroup.mem_map.mpr ⟨x, hKle (MonoidHom.mem_ker.mpr hx), rfl⟩

private theorem psi_eq_one_iff_k334 {N₀ N₁ : Subgroup G}
    {ψ : ↥N₀ →* ↥(CFSG.Quasithin.G6.coreMod 5)} (hψk : ψ.ker = N₁.subgroupOf N₀) {x : G}
    (hx : x ∈ N₀) : ψ ⟨x, hx⟩ = 1 ↔ x ∈ N₁ := by
  rw [← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf]

private theorem Q_le_normalizer_N₁_k334 {Q N₀ N₁ : Subgroup G} (h01 : N₁ ≤ N₀)
    (hN0Q : ⁅N₀, Q⁆ ≤ N₁) : Q ≤ Subgroup.normalizer (N₁ : Set G) :=
  Subgroup.le_normalizer_iff_commutator_le_left.mpr
    ((Subgroup.commutator_mono h01 le_rfl).trans hN0Q)

private theorem ker_le_inf_k334 {D Q : Subgroup G} (hD5 : IsAlt (Bar2 D) 5)
    (hDQ2 : D ⊓ Q = CFSG.Open.pCoreOf 2 D) {φ : ↥D →* alternatingGroup (Fin 5)}
    (hφs : Function.Surjective φ) {e : ↥D} (he : φ e = 1) : (e : G) ∈ D ⊓ Q := by
  rw [hDQ2]
  exact ker_le_pCoreOf_k334 hD5 hφs he

private theorem mem_frattini_iff_k334 {S : Subgroup G} (y : ↥S) :
    (y : G) ∈ frattiniOf S ↔ y ∈ frattini ↥S :=
  Subgroup.mem_map_iff_mem S.subtype_injective

private theorem le_N₁_of_comm_le_k334 {D N₀ N₁ Y : Subgroup G} (h01 : N₁ ≤ N₀)
    (hnat : NatA5Sec D N₀ N₁) (hY : Y ≤ N₀) (hYD : ⁅Y, D⁆ ≤ N₁) : Y ≤ N₁ := by
  obtain ⟨φ, ψ, hφs, hψs, hψk, hψeq⟩ := hnat
  intro y hy
  have hyN : y ∈ N₀ := hY hy
  have hfix : ∀ d : ↥D, CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5))
      (ψ ⟨y, hyN⟩) = ψ ⟨y, hyN⟩ := by
    intro d
    have hc : ⁅y, (d : G)⁆ ∈ N₁ := hYD (Subgroup.commutator_mem_commutator hy d.2)
    have hdy : (d : G) * y * (d : G)⁻¹ ∈ N₀ := by
      have e1 : (d : G) * y * (d : G)⁻¹ = (⁅y, (d : G)⁆)⁻¹ * y := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact N₀.mul_mem (N₀.inv_mem (h01 hc)) hyN
    have h1 := hψeq d ⟨y, hyN⟩ ⟨_, hdy⟩ rfl
    have h2 : ψ ⟨⁅y, (d : G)⁆, h01 hc⟩ = 1 := (psi_eq_one_iff_k334 hψk _).mpr hc
    have h3 : (⟨⁅y, (d : G)⁆, h01 hc⟩ : ↥N₀) = ⟨y, hyN⟩ * (⟨_, hdy⟩ : ↥N₀)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [h3, map_mul, map_inv, h1, mul_inv_eq_one] at h2
    exact h2.symm
  have hw : ψ ⟨y, hyN⟩ = 1 := by
    apply CFSG.CGT.PushingUpLit.SYMB.Delta5Fix.no_fixed
    intro σ hσ
    obtain ⟨d, hd⟩ := hφs ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ⟩
    have := hfix d
    rwa [show (φ d : Equiv.Perm (Fin 5)) = σ from congrArg Subtype.val hd] at this
  exact (psi_eq_one_iff_k334 hψk hyN).mp hw

private theorem comm_Q_R_le_N₁_k334 {D Q N₀ N₁ : Subgroup G} (h01 : N₁ ≤ N₀)
    (hSN0 : ⁅Q, D⁆ ≤ N₀) (hN0Q : ⁅N₀, Q⁆ ≤ N₁) (hD1 : ⁅D, N₁⁆ = ⊥)
    (hnat : NatA5Sec D N₀ N₁) : ⁅Q, D ⊓ Q⁆ ≤ N₁ := by
  set R := D ⊓ Q with hR
  have hN1Q : Q ≤ Subgroup.normalizer (N₁ : Set G) := Q_le_normalizer_N₁_k334 h01 hN0Q
  have hN1D : D ≤ Subgroup.normalizer (N₁ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr (by rw [hD1]; exact bot_le)
  have hRQ : R ≤ Q := inf_le_right
  have hRD : R ≤ D := inf_le_left
  have h1 : ⁅⁅R, D⁆, Q⁆ ≤ N₁ :=
    ((Subgroup.commutator_mono (Subgroup.commutator_mono hRQ le_rfl) le_rfl).trans
      (Subgroup.commutator_mono hSN0 le_rfl)).trans hN0Q
  have h2 : ⁅⁅D, Q⁆, R⁆ ≤ N₁ := by
    rw [Subgroup.commutator_comm D Q]
    exact (Subgroup.commutator_mono hSN0 hRQ).trans hN0Q
  have h3 : ⁅⁅Q, R⁆, D⁆ ≤ N₁ :=
    three_subgroups_le_k334 (N := N₁) (H₁ := Q) (H₂ := R) (H₃ := D) hN1Q (hRQ.trans hN1Q) hN1D
      h1 h2
  exact le_N₁_of_comm_le_k334 h01 hnat ((Subgroup.commutator_mono le_rfl hRD).trans hSN0) h3

private theorem exists_mem_comm_psi_eq_k334 {D Q N₀ N₁ : Subgroup G} (h01 : N₁ ≤ N₀)
    (hSN0 : ⁅Q, D⁆ ≤ N₀) (hSN : ⁅Q, D⁆ ≤ Subgroup.normalizer (N₁ : Set G))
    (hSN₁ : ⁅Q, D⁆ ⊔ N₁ = N₀) (ψ : ↥N₀ →* ↥(CFSG.Quasithin.G6.coreMod 5))
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = N₁.subgroupOf N₀)
    (w : ↥(CFSG.Quasithin.G6.coreMod 5)) :
    ∃ (s : G) (hs : s ∈ ⁅Q, D⁆), ψ ⟨s, hSN0 hs⟩ = w := by
  obtain ⟨n, hn⟩ := hψs w
  have hnS : (n : G) ∈ ⁅Q, D⁆ ⊔ N₁ := hSN₁ ▸ n.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSN] at hnS
  obtain ⟨s, hs, m, hm, hsm⟩ := hnS
  refine ⟨s, hs, ?_⟩
  have hprod : n = ⟨s, hSN0 hs⟩ * ⟨m, h01 hm⟩ := Subtype.ext hsm.symm
  rw [hprod, map_mul, (psi_eq_one_iff_k334 hψk (h01 hm)).mpr hm, mul_one] at hn
  exact hn

private theorem inj_of_split_k334 {E X : Type*} [Group E] [Finite E] [Group X] [Finite X]
    (η : E →* Equiv.Perm (Fin 5)) (hA : ∀ e, η e ∈ alternatingGroup (Fin 5))
    (hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, η e = σ)
    (hcomm : ∀ x y : X, x * y = y * x) (hX : ∀ x : X, x * x = 1)
    (act : E →* MulAut X) (hker : ∀ e, η e = 1 → ∀ x, act e x = x)
    (ψ : X →* ↥(CFSG.Quasithin.G6.coreMod 5)) (hψs : Function.Surjective ψ)
    (hψ : ∀ e x, ψ (act e x) = CFSG.Quasithin.G6.coreAct 5 (η e) (ψ x))
    (hfixK : ∀ e k, ψ k = 1 → act e k = k)
    (hgen : ∀ T : Subgroup X, (∀ e y, act e y * y⁻¹ ∈ T) → ∀ x, x ∈ T) :
    ∀ x, ψ x = 1 → x = 1 := by
  letI : CommGroup X := { (inferInstance : Group X) with mul_comm := hcomm }
  obtain ⟨s, hψs', hs'⟩ :=
    CFSG.CGT.PushingUpLit.SYMB.exists_equivariant_section η hA hs hX act hker ψ hψs hψ
  have hrange : ∀ e y, act e y * y⁻¹ ∈ s.range := by
    intro e y
    set w := ψ y with hw
    have hk : ψ (y * (s w)⁻¹) = 1 := by
      rw [map_mul, map_inv, hψs']
      exact mul_inv_cancel w
    have hfix := hfixK e _ hk
    have h1 : act e y = (y * (s w)⁻¹) * s (CFSG.Quasithin.G6.coreAct 5 (η e) w) := by
      have hy : y = (y * (s w)⁻¹) * s w := by simp
      conv_lhs => rw [hy]
      rw [map_mul, hfix, hs']
    refine ⟨CFSG.Quasithin.G6.coreAct 5 (η e) w * w⁻¹, ?_⟩
    rw [map_mul, map_inv, h1,
      show y * (s w)⁻¹ * s (CFSG.Quasithin.G6.coreAct 5 (η e) w) * y⁻¹ =
        (y * y⁻¹) * (s (CFSG.Quasithin.G6.coreAct 5 (η e) w) * (s w)⁻¹) by ac_rfl,
      mul_inv_cancel, one_mul]
  intro x hx
  obtain ⟨w, rfl⟩ := hgen s.range hrange x
  have hw1 : w = 1 := by
    rw [← hψs' w]
    exact hx
  rw [hw1, map_one]

private theorem exists_frattini_quot_action_k334 (P : Type*) [Group P] :
    ∃ A : MulAut P →* MulAut (P ⧸ frattini P),
      ∀ (e : MulAut P) (x : P), A e (QuotientGroup.mk x) = QuotientGroup.mk (e x) := by
  have hchar : ∀ e : MulAut P, (frattini P).map (e : P →* P) = frattini P := fun e =>
    Subgroup.characteristic_iff_map_eq.mp inferInstance e
  refine ⟨{ toFun := fun e => QuotientGroup.congr (frattini P) (frattini P) e (hchar e)
            map_one' := ?_
            map_mul' := ?_ }, fun e x => rfl⟩
  · ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.congr_mk]
      rfl
  · intro g h
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk]
      rfl

private theorem hgen_frattini_quot_k334 {E P : Type*} [Group E] [Group P] (act : E →* MulAut P)
    (A : MulAut P →* MulAut (P ⧸ frattini P))
    (hA' : ∀ (e : MulAut P) (x : P), A e (QuotientGroup.mk x) = QuotientGroup.mk (e x))
    (hgen : ∀ T : Subgroup P, (∀ e x, act e x * x⁻¹ ∈ T) → T = ⊤) :
    ∀ T : Subgroup (P ⧸ frattini P), (∀ e y, (A.comp act) e y * y⁻¹ ∈ T) → ∀ x, x ∈ T := by
  intro T hT x
  induction x using QuotientGroup.induction_on with
  | H y =>
    have hT' : ∀ e x, act e x * x⁻¹ ∈ T.comap (QuotientGroup.mk' (frattini P)) := by
      intro e x
      have h := hT e (QuotientGroup.mk x)
      have h2 : (A.comp act) e (QuotientGroup.mk x) = QuotientGroup.mk (act e x) :=
        hA' (act e) x
      rw [h2] at h
      rw [Subgroup.mem_comap, map_mul, map_inv]
      exact h
    have htop := hgen _ hT'
    have hy : y ∈ T.comap (QuotientGroup.mk' (frattini P)) := by rw [htop]; trivial
    exact hy

private theorem frattini_quot_fix_k334 {E P : Type*} [Group E] [Group P]
    (act : E →* MulAut P) (A : MulAut P →* MulAut (P ⧸ frattini P))
    (hA' : ∀ (e : MulAut P) (x : P), A e (QuotientGroup.mk x) = QuotientGroup.mk (e x))
    (e : E) (hker : ∀ x : P, act e x * x⁻¹ ∈ frattini P) :
    ∀ x : P ⧸ frattini P, (A.comp act) e x = x := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H y =>
    show A (act e) (QuotientGroup.mk y) = _
    rw [hA', QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv] using hker y

private theorem frattini_quot_fix_of_psi_k334 {E P : Type*} [Group E] [Group P]
    (act : E →* MulAut P) (A : MulAut P →* MulAut (P ⧸ frattini P))
    (hA' : ∀ (e : MulAut P) (x : P), A e (QuotientGroup.mk x) = QuotientGroup.mk (e x))
    (ψ : P →* ↥(CFSG.Quasithin.G6.coreMod 5))
    (ψ' : (P ⧸ frattini P) →* ↥(CFSG.Quasithin.G6.coreMod 5))
    (hψ' : ∀ x, ψ' (QuotientGroup.mk x) = ψ x)
    (hfixK : ∀ (e : E) (k : P), ψ k = 1 → act e k = k) :
    ∀ (e : E) (k : P ⧸ frattini P), ψ' k = 1 → (A.comp act) e k = k := by
  intro e k hk
  induction k using QuotientGroup.induction_on with
  | H y =>
    have hy : ψ y = 1 := by rw [← hψ']; exact hk
    show A (act e) (QuotientGroup.mk y) = _
    rw [hA', hfixK e y hy]

private theorem ker_le_frattini_of_split_k334 {E P : Type*} [Group E] [Finite E] [Group P]
    [Finite P] (hP : IsPGroup 2 P)
    (η : E →* Equiv.Perm (Fin 5)) (hA : ∀ e, η e ∈ alternatingGroup (Fin 5))
    (hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, η e = σ) (act : E →* MulAut P)
    (ψ : P →* ↥(CFSG.Quasithin.G6.coreMod 5)) (hψs : Function.Surjective ψ)
    (hψ : ∀ e x, ψ (act e x) = CFSG.Quasithin.G6.coreAct 5 (η e) (ψ x))
    (hfr : frattini P ≤ ψ.ker)
    (hker : ∀ e, η e = 1 → ∀ x, act e x * x⁻¹ ∈ frattini P)
    (hfixK : ∀ e k, ψ k = 1 → act e k = k)
    (hgen : ∀ T : Subgroup P, (∀ e x, act e x * x⁻¹ ∈ T) → T = ⊤) :
    ψ.ker ≤ frattini P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA'⟩ := exists_frattini_quot_action_k334 P
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : (P ⧸ frattini P) →* ↥(CFSG.Quasithin.G6.coreMod 5),
      ∀ x, ψ' (QuotientGroup.mk x) = ψ x :=
    ⟨QuotientGroup.lift (frattini P) ψ hfr, fun x => rfl⟩
  have hcomm : ∀ x y : P ⧸ frattini P, x * y = y * x := fun x y =>
    (CFSG.OrderReductions.FrattiniElementary.frattini_quotient_isMulCommutative 2 hP).is_comm.comm
      x y
  have hX : ∀ x : P ⧸ frattini P, x * x = 1 := fun x => by
    rw [← pow_two]
    exact CFSG.OrderReductions.FrattiniElementary.frattini_quotient_exponent 2 hP x
  have hker' : ∀ e, η e = 1 → ∀ x : P ⧸ frattini P, (A.comp act) e x = x :=
    fun e he => frattini_quot_fix_k334 act A hA' e (hker e he)
  have hs' : Function.Surjective ψ' := by
    intro w
    obtain ⟨y, hy⟩ := hψs w
    exact ⟨QuotientGroup.mk y, by rw [hψ']; exact hy⟩
  have hψ'' : ∀ e x, ψ' ((A.comp act) e x) = CFSG.Quasithin.G6.coreAct 5 (η e) (ψ' x) := by
    intro e y
    induction y using QuotientGroup.induction_on with
    | H y =>
      show ψ' (A (act e) (QuotientGroup.mk y)) = _
      rw [hA', hψ', hψ', hψ]
  have hfixK' : ∀ e (k : P ⧸ frattini P), ψ' k = 1 → (A.comp act) e k = k :=
    frattini_quot_fix_of_psi_k334 act A hA' ψ ψ' hψ' hfixK
  have hgen' := hgen_frattini_quot_k334 act A hA' hgen
  have key := inj_of_split_k334 η hA hs hcomm hX (A.comp act) hker' ψ' hs' hψ'' hfixK' hgen'
  intro x hx
  have h1 : (QuotientGroup.mk x : P ⧸ frattini P) = 1 := key _ (by rw [hψ']; exact hx)
  exact (QuotientGroup.eq_one_iff x).mp h1

private theorem top_of_comm_gen_k334 {D Q : Subgroup G} (hperf : ⁅D, D⁆ = D)
    (hQN : Q ≤ Subgroup.normalizer (D : Set G)) (act : ↥D →* MulAut ↥⁅Q, D⁆)
    (hact : ∀ (d : ↥D) (x : ↥⁅Q, D⁆), ((act d x : ↥⁅Q, D⁆) : G) = (d : G) * (x : G) * (d : G)⁻¹)
    (T : Subgroup ↥⁅Q, D⁆) (hT : ∀ (e : ↥D) (x : ↥⁅Q, D⁆), act e x * x⁻¹ ∈ T) : T = ⊤ := by
  have h1 : ⁅⁅Q, D⁆, D⁆ ≤ T.map (⁅Q, D⁆).subtype := Subgroup.commutator_le.mpr fun s hs d hd => by
    refine ⟨_, T.inv_mem (hT ⟨d, hd⟩ ⟨s, hs⟩), ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, hact]
    simp only [Subgroup.coe_inv, commutatorElement_def]
    group
  rw [comm_S_eq_self_k334 hperf hQN] at h1
  rw [eq_top_iff]
  intro x _
  exact (Subgroup.mem_map_iff_mem (⁅Q, D⁆).subtype_injective).mp (h1 x.2)

private theorem surjective_eta_k334 {D : Subgroup G} {φ : ↥D →* alternatingGroup (Fin 5)}
    (hφs : Function.Surjective φ) :
    ∀ σ ∈ alternatingGroup (Fin 5),
      ∃ e : ↥D, (alternatingGroup (Fin 5)).subtype (φ e) = σ := by
  intro σ hσ
  obtain ⟨e, he⟩ := hφs ⟨σ, hσ⟩
  exact ⟨e, congrArg Subtype.val he⟩

private theorem act_mul_inv_mem_frattini_k334 {D Q S : Subgroup G} (hD5 : IsAlt (Bar2 D) 5)
    (hDQ2 : D ⊓ Q = CFSG.Open.pCoreOf 2 D) {φ : ↥D →* alternatingGroup (Fin 5)}
    (hφs : Function.Surjective φ) (hSR : ⁅S, D ⊓ Q⁆ ≤ frattiniOf S)
    (act : ↥D →* MulAut ↥S)
    (hact : ∀ (d : ↥D) (x : ↥S), ((act d x : ↥S) : G) = (d : G) * (x : G) * (d : G)⁻¹)
    {e : ↥D} (he : φ e = 1) (x : ↥S) : act e x * x⁻¹ ∈ frattini ↥S := by
  have h1 : ⁅(x : G), (e : G)⁆ ∈ frattiniOf S :=
    hSR (Subgroup.commutator_mem_commutator x.2 (ker_le_inf_k334 hD5 hDQ2 hφs he))
  have h2 := (frattiniOf S).inv_mem h1
  rw [commutatorElement_inv] at h2
  rw [← mem_frattini_iff_k334, Subgroup.coe_mul, Subgroup.coe_inv, hact]
  exact h2

private theorem act_eq_of_psi_eq_one_k334 {D S N₁ : Subgroup G} (hD1 : ⁅D, N₁⁆ = ⊥)
    (act : ↥D →* MulAut ↥S)
    (hact : ∀ (d : ↥D) (x : ↥S), ((act d x : ↥S) : G) = (d : G) * (x : G) * (d : G)⁻¹)
    {B : Type*} [Group B] {ψ₀ : ↥S →* B} (hψ0 : ∀ x : ↥S, ψ₀ x = 1 ↔ (x : G) ∈ N₁)
    {e : ↥D} {k : ↥S} (hk : ψ₀ k = 1) : act e k = k := by
  have hc := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hD1 e.2) (k : G) ((hψ0 k).mp hk)
  apply Subtype.ext
  rw [hact, ← hc]
  group

private theorem S_inter_N₁_eq_frattini_k334 {D Q N₀ N₁ : Subgroup G}
    (hQ : IsPGroup 2 Q) (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hQN : Q ≤ Subgroup.normalizer (D : Set G)) (hperf : ⁅D, D⁆ = D)
    (hD5 : IsAlt (Bar2 D) 5) (hDQ2 : D ⊓ Q = CFSG.Open.pCoreOf 2 D)
    (h01 : N₁ ≤ N₀) (hSN0 : ⁅Q, D⁆ ≤ N₀) (hN0Q : ⁅N₀, Q⁆ ≤ N₁) (hD1 : ⁅D, N₁⁆ = ⊥)
    (hSN₁ : ⁅Q, D⁆ ⊔ N₁ = N₀) (hnat : NatA5Sec D N₀ N₁) :
    ⁅Q, D⁆ ⊓ N₁ = frattiniOf ⁅Q, D⁆ := by
  have hsq : ∀ x ∈ N₀, x ^ 2 ∈ N₁ := fun x hx => sq_mem_N₁_k334 hnat hx
  obtain ⟨φ, ψ, hφs, hψs, hψk, hψeq⟩ := hnat
  set S := ⁅Q, D⁆ with hS
  have hSQ : S ≤ Q := (comm_le_inf_k334 hDQ hQN).trans inf_le_right
  have hDN : D ≤ Subgroup.normalizer (S : Set G) := Subgroup.normalizer_commutator_ge_right Q D
  have hfrS : frattiniOf S ≤ S ⊓ N₁ := frattini_le_S_inter_N₁_k334 hQ hN0Q hSN0 hSQ hsq
  have hSR : ⁅S, D ⊓ Q⁆ ≤ frattiniOf S :=
    comm_S_R_le_frattini_k334 hQ hDQ hQN hperf hSN0 hN0Q hD1
  refine le_antisymm ?_ hfrS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let η : ↥D →* Equiv.Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp φ
  let act : ↥D →* MulAut ↥S := (Subgroup.normalizerMonoidHom S).comp (Subgroup.inclusion hDN)
  let ψ₀ : ↥S →* ↥(CFSG.Quasithin.G6.coreMod 5) := ψ.comp (Subgroup.inclusion hSN0)
  have hact : ∀ (d : ↥D) (x : ↥S), ((act d x : ↥S) : G) = (d : G) * (x : G) * (d : G)⁻¹ :=
    fun d x => rfl
  have hψ0 : ∀ x : ↥S, ψ₀ x = 1 ↔ (x : G) ∈ N₁ := fun x =>
    psi_eq_one_iff_k334 hψk (hSN0 x.2)
  have hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, η e = σ := surjective_eta_k334 hφs
  have hψs₀ : Function.Surjective ψ₀ := fun w => by
    obtain ⟨s, hs, hsw⟩ := exists_mem_comm_psi_eq_k334 h01 hSN0
      (hSQ.trans (Q_le_normalizer_N₁_k334 h01 hN0Q)) hSN₁ ψ hψs hψk w
    exact ⟨⟨s, hs⟩, hsw⟩
  have hψ₀ : ∀ e x, ψ₀ (act e x) = CFSG.Quasithin.G6.coreAct 5 (η e) (ψ₀ x) := fun e x =>
    hψeq e ⟨x, hSN0 x.2⟩ ⟨(act e x : G), hSN0 (act e x).2⟩ (hact e x)
  have hfr : frattini ↥S ≤ ψ₀.ker := fun x hx =>
    (hψ0 x).mpr (hfrS ((mem_frattini_iff_k334 x).mpr hx)).2
  have hker : ∀ e, η e = 1 → ∀ x, act e x * x⁻¹ ∈ frattini ↥S :=
    fun e he x => act_mul_inv_mem_frattini_k334 hD5 hDQ2 hφs hSR act hact (Subtype.ext he) x
  have hfixK : ∀ e k, ψ₀ k = 1 → act e k = k :=
    fun e k hk => act_eq_of_psi_eq_one_k334 hD1 act hact hψ0 hk
  have key : ψ₀.ker ≤ frattini ↥S :=
    ker_le_frattini_of_split_k334 (hQ.to_le hSQ) η (fun e => (φ e).2) hs act ψ₀ hψs₀ hψ₀ hfr
      hker hfixK (top_of_comm_gen_k334 hperf hQN act hact)
  intro x hx
  exact (mem_frattini_iff_k334 ⟨x, hx.1⟩).mpr
    (key (MonoidHom.mem_ker.mpr ((hψ0 ⟨x, hx.1⟩).mpr hx.2)))

private theorem exists_coboundary_k334 {D Q N₀ N₁ : Subgroup G}
    (hSN0 : ⁅Q, D⁆ ≤ N₀) (hRN₁ : ⁅Q, D ⊓ Q⁆ ≤ N₁)
    {φ : ↥D →* alternatingGroup (Fin 5)} {ψ : ↥N₀ →* ↥(CFSG.Quasithin.G6.coreMod 5)}
    (hφs : Function.Surjective φ) (hkerφ : ∀ e : ↥D, φ e = 1 → (e : G) ∈ D ⊓ Q)
    (hψk : ψ.ker = N₁.subgroupOf N₀)
    (hψeq : ∀ (d : ↥D) (n n' : ↥N₀), (n' : G) = (d : G) * n * (d : G)⁻¹ →
      ψ n' = CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) (ψ n))
    {q : G} (hq : q ∈ Q) :
    ∃ w : ↥(CFSG.Quasithin.G6.coreMod 5), ∀ (d : ↥D) (hm : ⁅q, (d : G)⁆ ∈ N₀),
      ψ ⟨⁅q, (d : G)⁆, hm⟩ =
        CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) w * w⁻¹ := by
  let η : ↥D →* Equiv.Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp φ
  have hmem : ∀ d : ↥D, ⁅q, (d : G)⁆ ∈ N₀ := fun d =>
    hSN0 (Subgroup.commutator_mem_commutator hq d.2)
  let c : ↥D → ↥(CFSG.Quasithin.G6.coreMod 5) := fun d => ψ ⟨⁅q, (d : G)⁆, hmem d⟩
  have hc : ∀ e e', c (e * e') = c e * CFSG.Quasithin.G6.coreAct 5 (η e) (c e') := by
    intro e e'
    have hm3 : (e : G) * ⁅q, (e' : G)⁆ * (e : G)⁻¹ ∈ N₀ :=
      hSN0 ((Subgroup.mem_normalizer_iff.mp (Subgroup.normalizer_commutator_ge_right Q D e.2) _).mp
        (Subgroup.commutator_mem_commutator hq e'.2))
    have hprod : (⟨⁅q, ((e * e' : ↥D) : G)⁆, hmem (e * e')⟩ : ↥N₀) =
        ⟨⁅q, (e : G)⁆, hmem e⟩ * ⟨(e : G) * ⁅q, (e' : G)⁆ * (e : G)⁻¹, hm3⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_mul_right_eq_mul_conj]
      group
    show ψ ⟨⁅q, ((e * e' : ↥D) : G)⁆, hmem (e * e')⟩ = _
    rw [hprod, map_mul, hψeq e ⟨_, hmem e'⟩ ⟨_, hm3⟩ rfl]
    rfl
  have hker : ∀ e, η e = 1 → c e = 1 := fun e he =>
    (psi_eq_one_iff_k334 hψk (hmem e)).mpr
      (hRN₁ (Subgroup.commutator_mem_commutator hq (hkerφ e (Subtype.ext he))))
  obtain ⟨w, hw⟩ := CFSG.CGT.PushingUpLit.SYMB.coho_A5 η (fun e => (φ e).2)
    (fun σ hσ => by
      obtain ⟨e, he⟩ := hφs ⟨σ, hσ⟩
      exact ⟨e, congrArg Subtype.val he⟩) c hc hker
  exact ⟨w, fun d _ => hw d⟩

private theorem psi_commutator_eq_k334 {D N₀ : Subgroup G}
    {φ : ↥D →* alternatingGroup (Fin 5)} {ψ : ↥N₀ →* ↥(CFSG.Quasithin.G6.coreMod 5)}
    (hψeq : ∀ (d : ↥D) (n n' : ↥N₀), (n' : G) = (d : G) * n * (d : G)⁻¹ →
      ψ n' = CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) (ψ n))
    (d : ↥D) {s : G} (hs0 : s ∈ N₀) (hsd : ⁅s, (d : G)⁆ ∈ N₀)
    (hdsd : (d : G) * s * (d : G)⁻¹ ∈ N₀)
    {w : ↥(CFSG.Quasithin.G6.coreMod 5)} (hsw : ψ ⟨s, hs0⟩ = w) :
    ψ ⟨⁅s, (d : G)⁆, hsd⟩ =
      w * (CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) w)⁻¹ := by
  have e1 : (⟨⁅s, (d : G)⁆, hsd⟩ : ↥N₀) =
      ⟨s, hs0⟩ * (⟨(d : G) * s * (d : G)⁻¹, hdsd⟩ : ↥N₀)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [e1, map_mul, map_inv, hψeq d ⟨s, hs0⟩ ⟨_, hdsd⟩ rfl, hsw]

private theorem psi_conj_commutator_eq_k334 {D Q N₀ N₁ : Subgroup G}
    (hN0Q : ⁅N₀, Q⁆ ≤ N₁) {ψ : ↥N₀ →* ↥(CFSG.Quasithin.G6.coreMod 5)}
    (hψk : ψ.ker = N₁.subgroupOf N₀) {q s : G} (hq : q ∈ Q)
    {d : ↥D} (hsd : ⁅s, (d : G)⁆ ∈ N₀)
    (hcq : q * ⁅s, (d : G)⁆ * q⁻¹ ∈ N₀)
    (hqa : ⁅q, ⁅s, (d : G)⁆⁆ ∈ N₀) :
    ψ ⟨q * ⁅s, (d : G)⁆ * q⁻¹, hcq⟩ = ψ ⟨⁅s, (d : G)⁆, hsd⟩ := by
  have hk : ψ ⟨⁅q, ⁅s, (d : G)⁆⁆, hqa⟩ = 1 := (psi_eq_one_iff_k334 hψk hqa).mpr
    (hN0Q (by rw [Subgroup.commutator_comm]; exact Subgroup.commutator_mem_commutator hq hsd))
  have e1 : (⟨q * ⁅s, (d : G)⁆ * q⁻¹, hcq⟩ : ↥N₀) =
      ⟨⁅q, ⁅s, (d : G)⁆⁆, hqa⟩ * ⟨⁅s, (d : G)⁆, hsd⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  rw [e1, map_mul, hk, one_mul]

private theorem comm_mul_mem_N₁_k334 {D Q N₀ N₁ : Subgroup G} (h01 : N₁ ≤ N₀)
    (hN0Q : ⁅N₀, Q⁆ ≤ N₁) (hSN0 : ⁅Q, D⁆ ≤ N₀) (hSQ : ⁅Q, D⁆ ≤ Q)
    {φ : ↥D →* alternatingGroup (Fin 5)} {ψ : ↥N₀ →* ↥(CFSG.Quasithin.G6.coreMod 5)}
    (hψk : ψ.ker = N₁.subgroupOf N₀)
    (hψeq : ∀ (d : ↥D) (n n' : ↥N₀), (n' : G) = (d : G) * n * (d : G)⁻¹ →
      ψ n' = CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) (ψ n))
    {q s : G} (hq : q ∈ Q) (hs : s ∈ ⁅Q, D⁆) {w : ↥(CFSG.Quasithin.G6.coreMod 5)}
    (hw : ∀ (d : ↥D) (hm : ⁅q, (d : G)⁆ ∈ N₀), ψ ⟨⁅q, (d : G)⁆, hm⟩ =
      CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) w * w⁻¹)
    (hsw : ψ ⟨s, hSN0 hs⟩ = w) (d : ↥D) : ⁅q * s, (d : G)⁆ ∈ N₁ := by
  have hQ0 : Q ≤ Subgroup.normalizer (N₀ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hN0Q.trans h01)
  have hqd : ⁅q, (d : G)⁆ ∈ N₀ := hSN0 (Subgroup.commutator_mem_commutator hq d.2)
  have hsd : ⁅s, (d : G)⁆ ∈ N₀ := hSN0 (Subgroup.commutator_mem_commutator (hSQ hs) d.2)
  have hdsd : (d : G) * s * (d : G)⁻¹ ∈ N₀ :=
    hSN0 ((Subgroup.mem_normalizer_iff.mp
      (Subgroup.normalizer_commutator_ge_right Q D d.2) s).mp hs)
  have hcq : q * ⁅s, (d : G)⁆ * q⁻¹ ∈ N₀ := (Subgroup.mem_normalizer_iff.mp (hQ0 hq) _).mp hsd
  have hqs : ⁅q * s, (d : G)⁆ ∈ N₀ := by
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact N₀.mul_mem hcq hqd
  have hqa : ⁅q, ⁅s, (d : G)⁆⁆ ∈ N₀ := by
    rw [commutatorElement_def]
    exact N₀.mul_mem hcq (N₀.inv_mem hsd)
  have h1 : ψ ⟨⁅s, (d : G)⁆, hsd⟩ =
      w * (CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) w)⁻¹ :=
    psi_commutator_eq_k334 hψeq d (hSN0 hs) hsd hdsd hsw
  have h2 : ψ ⟨q * ⁅s, (d : G)⁆ * q⁻¹, hcq⟩ = ψ ⟨⁅s, (d : G)⁆, hsd⟩ :=
    psi_conj_commutator_eq_k334 hN0Q hψk hq hsd hcq hqa
  have h3 : ψ ⟨⁅q * s, (d : G)⁆, hqs⟩ = 1 := by
    have e1 : (⟨⁅q * s, (d : G)⁆, hqs⟩ : ↥N₀) =
        ⟨q * ⁅s, (d : G)⁆ * q⁻¹, hcq⟩ * ⟨⁅q, (d : G)⁆, hqd⟩ :=
      Subtype.ext (commutatorElement_mul_left_eq_conj_mul q s d)
    rw [e1, map_mul, h2, h1, hw d hqd]
    rw [show w * (CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) w)⁻¹ *
        (CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) w * w⁻¹) =
        (w * w⁻¹) * ((CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) w)⁻¹ *
          CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) w) by ac_rfl,
      mul_inv_cancel, inv_mul_cancel, one_mul]
  exact (psi_eq_one_iff_k334 hψk hqs).mp h3

private theorem centralizes_of_comm_mem_N₁_k334 {D Q N₁ : Subgroup G} (hperf : ⁅D, D⁆ = D)
    (hD1 : ⁅D, N₁⁆ = ⊥) (hQ1 : Q ≤ Subgroup.normalizer (N₁ : Set G)) {y : G} (hy : y ∈ Q)
    (h : ∀ d ∈ D, ⁅y, d⁆ ∈ N₁) : y ∈ Subgroup.centralizer (D : Set G) := by
  have hconj : ∀ a ∈ Q, ∀ n ∈ N₁, a * n * a⁻¹ ∈ N₁ := fun a ha n hn =>
    (Subgroup.mem_normalizer_iff.mp (hQ1 ha) n).mp hn
  let Y : Subgroup G :=
    { carrier := {z | z ∈ Q ∧ ∀ d ∈ D, ⁅z, d⁆ ∈ N₁}
      one_mem' := ⟨Q.one_mem, fun d _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, fun d hd => by
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact N₁.mul_mem (hconj a ha.1 _ (hb.2 d hd)) (ha.2 d hd)⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, fun d hd => by
        have e1 : ⁅a⁻¹, d⁆ = a⁻¹ * (⁅a, d⁆)⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e1]
        have := hconj a⁻¹ (Q.inv_mem ha.1) _ (N₁.inv_mem (ha.2 d hd))
        simpa using this⟩ }
  have hY1 : ⁅Y, D⁆ ≤ N₁ := Subgroup.commutator_le.mpr fun z hz d hd => hz.2 d hd
  have hY2 : ⁅N₁, D⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hD1
  have hY := CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_two_step hperf hY1 hY2
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have h1 : ⁅y, d⁆ ∈ ⁅Y, D⁆ := Subgroup.commutator_mem_commutator ⟨hy, h⟩ hd
  rw [hY, Subgroup.mem_bot] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

private theorem Q_eq_sup_centralizer_k334 {D Q N₀ N₁ : Subgroup G}
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hQN : Q ≤ Subgroup.normalizer (D : Set G))
    (hperf : ⁅D, D⁆ = D) (hD5 : IsAlt (Bar2 D) 5) (hDQ2 : D ⊓ Q = CFSG.Open.pCoreOf 2 D)
    (h01 : N₁ ≤ N₀) (hSN0 : ⁅Q, D⁆ ≤ N₀) (hN0Q : ⁅N₀, Q⁆ ≤ N₁) (hD1 : ⁅D, N₁⁆ = ⊥)
    (hSN₁ : ⁅Q, D⁆ ⊔ N₁ = N₀) (hnat : NatA5Sec D N₀ N₁) :
    Q = ⁅Q, D⁆ ⊔ (Q ⊓ Subgroup.centralizer (D : Set G)) := by
  have hRN₁ : ⁅Q, D ⊓ Q⁆ ≤ N₁ := comm_Q_R_le_N₁_k334 h01 hSN0 hN0Q hD1 hnat
  obtain ⟨φ, ψ, hφs, hψs, hψk, hψeq⟩ := hnat
  have hSQ : ⁅Q, D⁆ ≤ Q := (comm_le_inf_k334 hDQ hQN).trans inf_le_right
  have hQ1 : Q ≤ Subgroup.normalizer (N₁ : Set G) := Q_le_normalizer_N₁_k334 h01 hN0Q
  refine le_antisymm ?_ (sup_le hSQ inf_le_left)
  intro q hq
  obtain ⟨w, hw⟩ := exists_coboundary_k334 hSN0 hRN₁ hφs
    (fun e he => ker_le_inf_k334 hD5 hDQ2 hφs he) hψk hψeq hq
  obtain ⟨s, hs, hsw⟩ := exists_mem_comm_psi_eq_k334 h01 hSN0 (hSQ.trans hQ1) hSN₁ ψ hψs hψk w
  have hqs : q * s ∈ Q ⊓ Subgroup.centralizer (D : Set G) :=
    ⟨Q.mul_mem hq (hSQ hs), centralizes_of_comm_mem_N₁_k334 hperf hD1 hQ1
      (Q.mul_mem hq (hSQ hs))
      (fun d hd => comm_mul_mem_N₁_k334 h01 hN0Q hSN0 hSQ hψk hψeq hq hs hw hsw ⟨d, hd⟩)⟩
  have hfin : q * s * s⁻¹ ∈ ⁅Q, D⁆ ⊔ (Q ⊓ Subgroup.centralizer (D : Set G)) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right hqs) (Subgroup.mem_sup_left (inv_mem hs))
  simpa using hfin

theorem k334 {D Q N₀ N₁ : Subgroup G}
    (hQ : IsPGroup 2 Q) (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hQN : Q ≤ Subgroup.normalizer (D : Set G)) (hperf : ⁅D, D⁆ = D)
    (hD5 : IsAlt (Bar2 D) 5) (hDQ2 : D ⊓ Q = CFSG.Open.pCoreOf 2 D)
    (h01 : N₁ ≤ N₀) (h0Q : N₀ ≤ Q)
    (h0 : D ⊔ Q ≤ Subgroup.normalizer (N₀ : Set G))
    (h1 : D ⊔ Q ≤ Subgroup.normalizer (N₁ : Set G))
    (hD1 : ⁅D, N₁⁆ = ⊥) (hQD : ⁅Q, D⁆ ≤ N₀) (hN0Q : ⁅N₀, Q⁆ ≤ N₁)
    (hnat : NatA5Sec D N₀ N₁) :
    Q = ⁅Q, D⁆ ⊔ (Q ⊓ Subgroup.centralizer (D : Set G)) ∧
    ⁅⁅Q, D⁆, Q ⊓ Subgroup.centralizer (D : Set G)⁆ = ⊥ ∧
    ⁅Q, D⁆ ⊓ N₁ = frattiniOf ⁅Q, D⁆ ∧ ⁅Q, D⁆ ⊔ N₁ = N₀ := by
  have hD0 : D ≤ Subgroup.normalizer (N₀ : Set G) := le_trans le_sup_left h0
  have hSN₁ : ⁅Q, D⁆ ⊔ N₁ = N₀ := comm_S_sup_N₁_k334 h01 h0Q hD0 hQD hnat
  refine ⟨?_, ?_, ?_, hSN₁⟩
  · exact Q_eq_sup_centralizer_k334 hDQ hQN hperf hD5 hDQ2 h01 hQD hN0Q hD1 hSN₁ hnat
  · exact comm_S_centralizer_D_k334 hQ hDQ hQN hperf h01 hQD hN0Q hD1
  · exact S_inter_N₁_eq_frattini_k334 hQ hDQ hQN hperf hD5 hDQ2 h01 hQD hN0Q hD1 hSN₁ hnat

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
