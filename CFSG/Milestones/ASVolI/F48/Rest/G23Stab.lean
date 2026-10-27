module

public import Certificates.Certificate7763
public import Certificates.Certificate7764
public import CFSG.Milestones.ASVolI.F48.Rest.G23FactsBase
public import CFSG.Milestones.ASVolI.F48.Rest.Perm

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates

attribute [local irreducible] burnsideF48t_g23LArr burnsideF48t_g23Tau burnsideF48t_g23GensArr
  burnsideF48t_g23PtsStr

section Generic

variable {N : ℕ}

theorem burnsideF48t_permOfArr_mem_arrGen {O : Array (Array ℕ)} {t : Array ℕ} (ht : t ∈ O) :
    CFSG.Monster.B.Co2.permOfArr N t ∈ arrGen N O := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ht
  exact Subgroup.subset_closure ⟨k, hk, by rw [getElem!_pos O k hk]⟩

theorem burnsideF48t_arrGen_le {O : Array (Array ℕ)} {H : Subgroup (Equiv.Perm (Fin N))}
    (h : ∀ t ∈ O, CFSG.Monster.B.Co2.permOfArr N t ∈ H) : arrGen N O ≤ H := by
  rw [arrGen, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact h _ (by rw [getElem!_pos O k hk]; exact Array.getElem_mem hk)

theorem burnsideF48t_mem_of_closedL {gs : Array (Array ℕ)} {σ : ℕ → Equiv.Perm (Fin N)}
    (hrep : ∀ s < gs.size, PRep N gs[s]! (σ s)) {E : List (Array ℕ)}
    (h : burnsideF48t_closedL N gs E = true) :
    ∀ g ∈ Subgroup.closure (Set.range fun s : Fin gs.size => σ s), burnsideF48t_arr g ∈ E := by
  unfold burnsideF48t_closedL at h
  simp only [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hP := CFSG.Quasithin.closure_subset_of_right_closed
    (S := Set.range fun s : Fin gs.size => σ s)
    (P := {g | E.contains (burnsideF48t_arr g) = true})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    (by show E.contains (burnsideF48t_arr 1) = true; rw [← burnsideF48t_pid_arr]; exact h1)
    (by
      rintro p hp _ ⟨s, rfl⟩
      show E.contains (burnsideF48t_arr (p * σ s)) = true
      have hpE : burnsideF48t_arr p ∈ E := List.contains_iff_mem.1 hp
      have := h2 _ hpE s s.2
      have e : gs[(s : ℕ)]'s.2 = gs[(s : ℕ)]! := (getElem!_pos gs (s : ℕ) s.2).symm
      rwa [e, burnsideF48t_pcomp_arr (burnsideF48t_prep_arr p) (hrep s s.2)] at this)
  intro g hg
  exact List.contains_iff_mem.1 (hP hg)

theorem burnsideF48t_getElem!_toArray_map {α β : Type*} [Inhabited β] (f : α → β) (l : List α)
    {j : ℕ} (hj : j < l.length) (d : α) : ((l.map f).toArray)[j]! = f (l.getD j d) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem burnsideF48t_max_of_stab {X P R : Subgroup (Equiv.Perm (Fin N))} {pt : Fin N}
    (hP : P = X ⊓ MulAction.stabilizer (Equiv.Perm (Fin N)) pt)
    (hcov : ∀ g ∈ X, g pt ≠ pt → ∃ q ∈ P, ∃ h ∈ X, q (h pt) = g pt ∧
      ∀ Q : Subgroup (Equiv.Perm (Fin N)), P ≤ Q → h ∈ Q → Q ≤ X → Q = X)
    (hlt : P < R) (hRX : R ≤ X) : R = X := by
  obtain ⟨g, hgR, hgP⟩ := SetLike.exists_of_lt hlt
  have hgX := hRX hgR
  have hgpt : g pt ≠ pt := fun he => hgP (by
    rw [hP]
    exact ⟨hgX, MulAction.mem_stabilizer_iff.2 (by rw [Equiv.Perm.smul_def]; exact he)⟩)
  obtain ⟨q, hqP, h, hhX, hqh, hgen⟩ := hcov g hgX hgpt
  have hqX : q ∈ X := by
    rw [hP] at hqP
    exact hqP.1
  have hu : h⁻¹ * q⁻¹ * g ∈ P := by
    rw [hP]
    refine ⟨X.mul_mem (X.mul_mem (X.inv_mem hhX) (X.inv_mem hqX)) hgX,
      MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [Equiv.Perm.smul_def]
    simp only [Equiv.Perm.mul_apply]
    rw [← hqh]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  have hhR : h ∈ R := by
    have e : h = q⁻¹ * g * (h⁻¹ * q⁻¹ * g)⁻¹ := by group
    rw [e]
    exact R.mul_mem (R.mul_mem (R.inv_mem (hlt.le hqP)) hgR) (R.inv_mem (hlt.le hu))
  exact hgen R hlt.le hhR hRX

theorem burnsideF48t_mem_normalizer_of_conj {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : H → H := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hx⟩
  have := congrArg Subtype.val hy
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact y.2

end Generic

@[expose] def burnsideF48t_g23pA : Fin 728 := ⟨0, by norm_num⟩

@[expose] def burnsideF48t_g23pB : Fin 728 := ⟨364, by norm_num⟩

theorem burnsideF48t_g23_pA_eq : burnsideF48t_g23pA = 0 := rfl

theorem burnsideF48t_g23_pB_eq : burnsideF48t_g23pB = 364 := rfl

section Model

theorem burnsideF48t_g23_X_lt {g : Equiv.Perm (Fin 728)} (hg : g ∈ burnsideF48t_g23X)
    {x : Fin 728} (hx : (x : ℕ) < 364) : ((g x : Fin 728) : ℕ) < 364 :=
  Certificates.certificate7763.1 g hg x hx

theorem burnsideF48t_g23_X_ge {g : Equiv.Perm (Fin 728)} (hg : g ∈ burnsideF48t_g23X)
    {x : Fin 728} (hx : 364 ≤ (x : ℕ)) : 364 ≤ ((g x : Fin 728) : ℕ) := by
  by_contra h
  have := burnsideF48t_g23_X_lt (burnsideF48t_g23X.inv_mem hg) (not_le.1 h)
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at this
  omega

theorem burnsideF48t_g23_P1'_le_X : burnsideF48t_g23P1' ≤ burnsideF48t_g23X := by
  rw [burnsideF48t_g23_P1'_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  have hk : (k : ℕ) < 3 := burnsideF48t_g23_P1Arr.1 ▸ k.2
  exact burnsideF48t_g23_σ_mem (by unfold burnsideF48t_g23P1Idx; omega)

theorem burnsideF48t_g23_σ_fix :
    burnsideF48t_g23σ 0 burnsideF48t_g23pA = burnsideF48t_g23pA ∧
    burnsideF48t_g23σ 0 burnsideF48t_g23pB = burnsideF48t_g23pB ∧
    burnsideF48t_g23σ 1 burnsideF48t_g23pA = burnsideF48t_g23pA ∧
    burnsideF48t_g23σ 1 burnsideF48t_g23pB = burnsideF48t_g23pB ∧
    burnsideF48t_g23σ 2 burnsideF48t_g23pA = burnsideF48t_g23pA ∧
    burnsideF48t_g23σ 3 burnsideF48t_g23pB = burnsideF48t_g23pB ∧
    burnsideF48t_g23σ 3 burnsideF48t_g23pA ≠ burnsideF48t_g23pA ∧
    burnsideF48t_g23σ 2 burnsideF48t_g23pB ≠ burnsideF48t_g23pB := by
  rw [burnsideF48t_g23_pA_eq, burnsideF48t_g23_pB_eq]
  exact Certificates.certificate7762.2.2.2.2.2.2.2.2.2.2.2.1

theorem burnsideF48t_g23_P1Idx_cases (k : Fin burnsideF48t_g23P1Arr.size) :
    burnsideF48t_g23P1Idx k = 0 ∨ burnsideF48t_g23P1Idx k = 1 ∨ burnsideF48t_g23P1Idx k = 2 := by
  have : (k : ℕ) < 3 := burnsideF48t_g23_P1Arr.1 ▸ k.2
  unfold burnsideF48t_g23P1Idx
  omega

theorem burnsideF48t_g23_P2Idx_cases (k : Fin burnsideF48t_g23P2Arr.size) :
    burnsideF48t_g23P2Idx k = 0 ∨ burnsideF48t_g23P2Idx k = 1 ∨ burnsideF48t_g23P2Idx k = 3 := by
  have : (k : ℕ) < 3 := burnsideF48t_g23_P2Arr.1 ▸ k.2
  unfold burnsideF48t_g23P2Idx
  omega

theorem burnsideF48t_g23_P1'_le_stab : burnsideF48t_g23P1' ≤
    MulAction.stabilizer (Equiv.Perm (Fin 728)) burnsideF48t_g23pA := by
  rw [burnsideF48t_g23_P1'_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨f0, -, f1, -, f2, -⟩ := burnsideF48t_g23_σ_fix
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  rcases burnsideF48t_g23_P1Idx_cases k with h | h | h <;> simp only [h] <;> assumption

theorem burnsideF48t_g23_P1'_eq : burnsideF48t_g23P1' =
    burnsideF48t_g23X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 728)) burnsideF48t_g23pA :=
  Certificates.certificate7763.2.1

theorem burnsideF48t_g23_P2'_eq : burnsideF48t_g23P2' =
    burnsideF48t_g23X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 728)) burnsideF48t_g23pB :=
  Certificates.certificate7763.2.2.1

theorem burnsideF48t_g23_B'_eq : burnsideF48t_g23B' = burnsideF48t_g23P1' ⊓ burnsideF48t_g23P2' :=
  Certificates.certificate7763.2.2.2.1

theorem burnsideF48t_g23_P1'_max {R : Subgroup (Equiv.Perm (Fin 728))}
    (hlt : burnsideF48t_g23P1' < R) (hRX : R ≤ burnsideF48t_g23X) : R = burnsideF48t_g23X :=
  Certificates.certificate7763.2.2.2.2.1 R hlt hRX

theorem burnsideF48t_g23_P2'_max {R : Subgroup (Equiv.Perm (Fin 728))}
    (hlt : burnsideF48t_g23P2' < R) (hRX : R ≤ burnsideF48t_g23X) : R = burnsideF48t_g23X :=
  Certificates.certificate7763.2.2.2.2.2.1 R hlt hRX

end Model

section Norm

theorem burnsideF48t_g23_S0'_le_X : burnsideF48t_g23S0' ≤ burnsideF48t_g23X := by
  refine Certificates.certificate7762.2.2.2.2.2.2.1.trans ?_
  rw [burnsideF48t_g23_B'_eq]
  exact inf_le_left.trans burnsideF48t_g23_P1'_le_X

theorem burnsideF48t_g23_S0'_fix {s : Equiv.Perm (Fin 728)} (hs : s ∈ burnsideF48t_g23S0') :
    s burnsideF48t_g23pA = burnsideF48t_g23pA ∧ s burnsideF48t_g23pB = burnsideF48t_g23pB := by
  rw [burnsideF48t_g23_pA_eq, burnsideF48t_g23_pB_eq]
  exact Certificates.certificate7762.2.2.2.2.2.2.2.2.2.2.2.2.1 s hs

theorem burnsideF48t_g23_S0'_moves {p : Fin 728} (h0 : p ≠ burnsideF48t_g23pA)
    (h364 : p ≠ burnsideF48t_g23pB) : ∃ s ∈ burnsideF48t_g23S0', s p ≠ p :=
  Certificates.certificate7762.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p h0 h364

theorem burnsideF48t_g23_fix_of_norm {g : Equiv.Perm (Fin 728)} (hg : g ∈ burnsideF48t_g23X)
    (hn : ∀ s ∈ burnsideF48t_g23S0', g⁻¹ * s * g ∈ burnsideF48t_g23S0') :
    g burnsideF48t_g23pA = burnsideF48t_g23pA ∧ g burnsideF48t_g23pB = burnsideF48t_g23pB := by
  have hfixed : ∀ x, (x = burnsideF48t_g23pA ∨ x = burnsideF48t_g23pB) →
      (g x = burnsideF48t_g23pA ∨ g x = burnsideF48t_g23pB) := by
    intro x hx
    by_contra hne
    rw [not_or] at hne
    obtain ⟨s, hs, hsx⟩ := burnsideF48t_g23_S0'_moves hne.1 hne.2
    have h1 := burnsideF48t_g23_S0'_fix (hn s hs)
    apply hsx
    have : (g⁻¹ * s * g) x = x := by rcases hx with rfl | rfl; exacts [h1.1, h1.2]
    simp only [Equiv.Perm.mul_apply] at this
    calc s (g x) = g (g⁻¹ (s (g x))) := by simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
      _ = g x := by rw [this]
  have hA := hfixed burnsideF48t_g23pA (Or.inl rfl)
  have hB := hfixed burnsideF48t_g23pB (Or.inr rfl)
  have hlt : ((g burnsideF48t_g23pA : Fin 728) : ℕ) < 364 :=
    burnsideF48t_g23_X_lt hg (show ((burnsideF48t_g23pA : Fin 728) : ℕ) < 364 by decide)
  have hge : 364 ≤ ((g burnsideF48t_g23pB : Fin 728) : ℕ) :=
    burnsideF48t_g23_X_ge hg (show 364 ≤ ((burnsideF48t_g23pB : Fin 728) : ℕ) by decide)
  refine ⟨hA.resolve_right fun h => ?_, hB.resolve_left fun h => ?_⟩
  · rw [h] at hlt; exact absurd hlt (by decide)
  · rw [h] at hge; exact absurd hge (by decide)

theorem burnsideF48t_g23_B'_le_normalizer :
    burnsideF48t_g23B' ≤ Subgroup.normalizer (burnsideF48t_g23S0' : Set (Equiv.Perm (Fin 728))) :=
  Certificates.certificate7763.2.2.2.2.2.2

end Norm

section Tau

theorem burnsideF48t_g23_τ_conj_mem {g : Equiv.Perm (Fin 728)} (hg : g ∈ burnsideF48t_g23X) :
    burnsideF48t_g23τ * g * burnsideF48t_g23τ⁻¹ ∈ burnsideF48t_g23X := by
  rw [burnsideF48t_g23_X_eq] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨s, hs⟩, rfl⟩ := hx
    exact Certificates.certificate7762.2.2.2.2.2.1 s hs
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact burnsideF48t_g23X.one_mem
  | mul a b _ _ ha hb =>
    have e : burnsideF48t_g23τ * (a * b) * burnsideF48t_g23τ⁻¹ =
        (burnsideF48t_g23τ * a * burnsideF48t_g23τ⁻¹) * (burnsideF48t_g23τ * b * burnsideF48t_g23τ⁻¹) := by
      group
    rw [e]
    exact burnsideF48t_g23X.mul_mem ha hb
  | inv a _ ha =>
    have e : burnsideF48t_g23τ * a⁻¹ * burnsideF48t_g23τ⁻¹ =
        (burnsideF48t_g23τ * a * burnsideF48t_g23τ⁻¹)⁻¹ := by group
    rw [e]
    exact burnsideF48t_g23X.inv_mem ha

theorem burnsideF48t_g23_τ_pA : 364 ≤ ((burnsideF48t_g23τ burnsideF48t_g23pA : Fin 728) : ℕ) := by
  rw [burnsideF48t_g23_pA_eq]
  exact Certificates.certificate7762.2.2.2.2.2.2.2.2.2.2.1

theorem burnsideF48t_g23_P1'_nofix (q : Fin 728) (hq : 364 ≤ (q : ℕ)) :
    ∃ g ∈ burnsideF48t_g23P1', g q ≠ q :=
  Certificates.certificate7762.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q hq

end Tau

section K

theorem burnsideF48t_g23_K'_cases {c : Equiv.Perm (Fin 728)} (hc : c ∈ burnsideF48t_g23K') :
    c = 1 ∨ c = burnsideF48t_g23κ 0 ∨ c = burnsideF48t_g23κ 1 ∨
      c = burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1 :=
  Certificates.certificate7764.1 c hc

theorem burnsideF48t_g23_xred {x : Equiv.Perm (Fin 728)} (hx : x ∈ burnsideF48t_g23P1')
    (hx2 : x ∉ burnsideF48t_g23P2') (hxK : ∀ k ∈ burnsideF48t_g23K', x * k * x⁻¹ ∈ burnsideF48t_g23K')
    (_hxx : x * x ∈ burnsideF48t_g23K') : (burnsideF48t_g23σ 2)⁻¹ * x ∈ burnsideF48t_g23K' :=
  Certificates.certificate7764.2.1 x hx hx2 hxK

theorem burnsideF48t_g23_yred {y : Equiv.Perm (Fin 728)} (hy : y ∈ burnsideF48t_g23P2')
    (hy1 : y ∉ burnsideF48t_g23P1') (hyK : ∀ k ∈ burnsideF48t_g23K', y * k * y⁻¹ ∈ burnsideF48t_g23K')
    (_hyy : y * y ∈ burnsideF48t_g23K') : (burnsideF48t_g23σ 3)⁻¹ * y ∈ burnsideF48t_g23K' :=
  Certificates.certificate7764.2.2 y hy hy1 hyK

theorem burnsideF48t_g23_K'_le_B' : burnsideF48t_g23K' ≤ burnsideF48t_g23B' :=
  Certificates.certificate7762.2.2.2.2.2.2.2.1

end K

end CFSG.ASVolI
