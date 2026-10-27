module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSetup
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSeven
public import CFSG.LocalAnalysis.WeakClosure81.NineTwoF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

@[expose] def nineSwapStab (V A S : Subgroup G) : Subgroup G :=
  nineDeltaStab V S ⊓ normalizer (V : Set G) ⊓ normalizer (A : Set G)

@[expose] def nineSwapCV (V A S : Subgroup G) : Subgroup G :=
  nineSwapStab V A S ⊓ centralizer (V : Set G)

@[expose] def nineSwapCA (V A S : Subgroup G) : Subgroup G :=
  nineSwapStab V A S ⊓ centralizer (A : Set G)

private theorem nineThree_conj_sup (P Q : Subgroup G) (g : G) :
    conjSubgroup (P ⊔ Q) g = conjSubgroup P g ⊔ conjSubgroup Q g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_sup _ _ _

private theorem nineThree_conj_mem_nineSwapStab {c g : G}
    (hg : g ∈ nineDeltaStab V S) (hV : conjSubgroup V g = A)
    (hA : conjSubgroup A g = V) (hc : c ∈ nineSwapStab V A S) :
    g⁻¹ * c * g ∈ nineSwapStab V A S := by
  obtain ⟨⟨hcΔ, hcV⟩, hcA⟩ := hc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (nineDeltaStab V S).mul_mem
      ((nineDeltaStab V S).mul_mem ((nineDeltaStab V S).inv_mem hg) hcΔ) hg
  · have h1 : g⁻¹ * c * g ∈ conjSubgroup (normalizer (A : Set G)) g := by
      rw [mem_conjSubgroup_iff]
      have e : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
      rw [e]
      exact hcA
    rwa [E3.conjSubgroup_normalizer, hA] at h1
  · have h1 : g⁻¹ * c * g ∈ conjSubgroup (normalizer (V : Set G)) g := by
      rw [mem_conjSubgroup_iff]
      have e : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
      rw [e]
      exact hcV
    rwa [E3.conjSubgroup_normalizer, hV] at h1

private theorem nineThree_conj_mem_nineSwapCV {c g : G}
    (hg : g ∈ nineDeltaStab V S) (hV : conjSubgroup V g = A)
    (hA : conjSubgroup A g = V) (hc : c ∈ nineSwapCV V A S) :
    g⁻¹ * c * g ∈ nineSwapCA V A S := by
  obtain ⟨hcStab, hcC⟩ := hc
  refine ⟨nineThree_conj_mem_nineSwapStab hg hV hA hcStab, ?_⟩
  have h1 : g⁻¹ * c * g ∈ conjSubgroup (centralizer (V : Set G)) g := by
    rw [mem_conjSubgroup_iff]
    have e : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
    rw [e]
    exact hcC
  rwa [E3.conjSubgroup_centralizer, hV] at h1

private theorem nineThree_conj_mem_nineSwapCA {c g : G}
    (hg : g ∈ nineDeltaStab V S) (hV : conjSubgroup V g = A)
    (hA : conjSubgroup A g = V) (hc : c ∈ nineSwapCA V A S) :
    g⁻¹ * c * g ∈ nineSwapCV V A S := by
  obtain ⟨hcStab, hcC⟩ := hc
  refine ⟨nineThree_conj_mem_nineSwapStab hg hV hA hcStab, ?_⟩
  have h1 : g⁻¹ * c * g ∈ conjSubgroup (centralizer (A : Set G)) g := by
    rw [mem_conjSubgroup_iff]
    have e : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
    rw [e]
    exact hcC
  rwa [E3.conjSubgroup_centralizer, hA] at h1

theorem conj_nineSwapCV (hg : g ∈ nineDeltaStab V S) (hV : conjSubgroup V g = A)
    (hA : conjSubgroup A g = V) :
    conjSubgroup (nineSwapCV V A S) g = nineSwapCA V A S := by
  apply le_antisymm
  · intro y hy
    have hc : g * y * g⁻¹ ∈ nineSwapCV V A S := mem_conjSubgroup_iff.mp hy
    have h := nineThree_conj_mem_nineSwapCV hg hV hA hc
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at h
  · have hg' : g⁻¹ ∈ nineDeltaStab V S := Subgroup.inv_mem _ hg
    have hV' : conjSubgroup V g⁻¹ = A := by rw [← hA, nineThree_conj_inv]
    have hA' : conjSubgroup A g⁻¹ = V := by rw [← hV, nineThree_conj_inv]
    intro y hy
    have h := nineThree_conj_mem_nineSwapCA hg' hV' hA' hy
    rw [mem_conjSubgroup_iff]
    simpa using h

theorem conj_nineSwapCA (hg : g ∈ nineDeltaStab V S) (hV : conjSubgroup V g = A)
    (hA : conjSubgroup A g = V) :
    conjSubgroup (nineSwapCA V A S) g = nineSwapCV V A S := by
  apply le_antisymm
  · intro y hy
    have hc : g * y * g⁻¹ ∈ nineSwapCA V A S := mem_conjSubgroup_iff.mp hy
    have h := nineThree_conj_mem_nineSwapCA hg hV hA hc
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at h
  · have hg' : g⁻¹ ∈ nineDeltaStab V S := Subgroup.inv_mem _ hg
    have hV' : conjSubgroup V g⁻¹ = A := by rw [← hA, nineThree_conj_inv]
    have hA' : conjSubgroup A g⁻¹ = V := by rw [← hV, nineThree_conj_inv]
    intro y hy
    have h := nineThree_conj_mem_nineSwapCV hg' hV' hA' hy
    rw [mem_conjSubgroup_iff]
    simpa using h

private theorem nineThree_isSylowIn_conj (g : G) {P H : Subgroup G}
    (h : IsSylowIn 2 P H) : IsSylowIn 2 (conjSubgroup P g) (conjSubgroup H g) := by
  have h' := (E1.isSylowIn_map_mulEquiv (p := 2) (MulAut.conj g⁻¹)).mpr h
  simpa only [CFSG.Quasithin.conjSubgroup] using h'

theorem Nine3Core.isSylowIn_nineSwapCA (h : Nine3Core V T A K S X p) :
    IsSylowIn 2 (T ⊓ centralizer (A : Set G)) (nineSwapCA V A S) := by
  have hP : T ⊓ centralizer (A : Set G) ≤ nineSwapCA V A S := by
    intro x hx
    exact ⟨⟨⟨h.S_le_nineDeltaStab (nine_three_four_centralizer h hx),
      (h.syl.le hx).1⟩, (Subgroup.centralizer_le_normalizer (A : Set G)) hx.2⟩, hx.2⟩
  have hCA : nineSwapCA V A S ≤ normalizer (V : Set G) ⊓ centralizer (A : Set G) :=
    fun x hx => ⟨hx.1.1.2, hx.2⟩
  exact nineThree_isSylowIn_of_le h.syl hP hCA

theorem Nine3Core.exists_isSylowIn_nineSwap (h : Nine3Core V T A K S X p) :
    ∃ Y : Subgroup G, IsSylowIn 2 Y (nineSwapCV V A S ⊔ nineSwapCA V A S) ∧
      (T ⊓ centralizer (A : Set G)) ⊔
        (S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G)) ≤ Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : T ⊓ centralizer (A : Set G) ≤ nineSwapCV V A S ⊔ nineSwapCA V A S :=
    le_sup_of_le_right (Nine3Core.isSylowIn_nineSwapCA h).le
  have hS0 : S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G) ≤
      nineSwapCV V A S ⊔ nineSwapCA V A S := by
    refine le_sup_of_le_left (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_)
    · exact (inf_le_left.trans inf_le_left).trans h.S_le_nineDeltaStab
    · exact (inf_le_left.trans inf_le_left).trans (h.leS.trans h.h9.sylow.le)
    · exact inf_le_right
    · exact inf_le_left.trans inf_le_right
  have hle : (T ⊓ centralizer (A : Set G)) ⊔
      (S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G)) ≤ S :=
    sup_le (nine_three_four_centralizer h) (inf_le_left.trans inf_le_left)
  have h2 : IsPGroup 2 ((T ⊓ centralizer (A : Set G)) ⊔
      (S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G)) : Subgroup G) :=
    h.h9.sylow.isPGroup.to_le (hle.trans h.leS)
  obtain ⟨Y, hY, hPY⟩ := exists_isSylowIn_ge 2 (sup_le hP hS0) h2
  exact ⟨Y, hY, hPY⟩

theorem Nine3Core.exists_swap_normalizing (h : Nine3Core V T A K S X p) {Y : Subgroup G}
    (hY : IsSylowIn 2 Y (nineSwapCV V A S ⊔ nineSwapCA V A S)) :
    ∃ g ∈ nineDeltaStab V S, conjSubgroup V g = A ∧ conjSubgroup A g = V ∧
      conjSubgroup Y g = Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₁, hg₁N, hVg₁, hAg₁⟩ := nine_three_two_transitive h h.V_mem_nineDelta
    h.A_mem_nineDelta h.A_mem_nineDelta h.V_mem_nineDelta h.ne.symm h.ne
  have hChat : conjSubgroup (nineSwapCV V A S ⊔ nineSwapCA V A S) g₁ =
      nineSwapCV V A S ⊔ nineSwapCA V A S := by
    rw [nineThree_conj_sup, conj_nineSwapCV hg₁N hVg₁ hAg₁,
      conj_nineSwapCA hg₁N hVg₁ hAg₁, sup_comm]
  have hYg₁ : IsSylowIn 2 (conjSubgroup Y g₁) (nineSwapCV V A S ⊔ nineSwapCA V A S) := by
    have h1 := nineThree_isSylowIn_conj g₁ hY
    rwa [hChat] at h1
  obtain ⟨c, hcChat, hle⟩ := E3.exists_le_conj_of_isSylowIn hY hYg₁.le hYg₁.isPGroup
  have heq : conjSubgroup Y g₁ = conjSubgroup Y c := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    simp [E3.card_conjSubgroup]
  have hYgc : conjSubgroup Y (g₁ * c⁻¹) = Y := by
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, heq, nineThree_conj_inv]
  have hcStab : c ∈ nineSwapStab V A S :=
    (sup_le (inf_le_left : nineSwapCV V A S ≤ nineSwapStab V A S)
      (inf_le_left : nineSwapCA V A S ≤ nineSwapStab V A S)) hcChat
  have hcN : c ∈ nineDeltaStab V S := hcStab.1.1
  have hcV : c ∈ normalizer (V : Set G) := hcStab.1.2
  have hcA : c ∈ normalizer (A : Set G) := hcStab.2
  refine ⟨g₁ * c⁻¹, Subgroup.mul_mem _ hg₁N (Subgroup.inv_mem _ hcN), ?_, ?_, hYgc⟩
  · rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, hVg₁,
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ hcA)]
  · rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, hAg₁,
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ hcV)]

private theorem nineThree_S0_le_conj_of_swap (h : Nine3Core V T A K S X p)
    {h' : G} {Y : Subgroup G} (hh' : h' ∈ nineDeltaStab V S)
    (hV' : conjSubgroup V h' = A) (hA' : conjSubgroup A h' = V)
    (hY' : conjSubgroup Y h' = Y)
    (hY : IsSylowIn 2 Y (nineSwapCV V A S ⊔ nineSwapCA V A S))
    (hPS0Y : (T ⊓ centralizer (A : Set G)) ⊔
      (S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G)) ≤ Y) :
    S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G) ≤ conjSubgroup S h' := by
  have hS0Y : S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G) ≤ Y :=
    le_sup_right.trans hPS0Y
  have hPY : T ⊓ centralizer (A : Set G) ≤ Y := le_sup_left.trans hPS0Y
  have hh'inv : h'⁻¹ ∈ nineDeltaStab V S := Subgroup.inv_mem _ hh'
  have hV'inv : conjSubgroup V h'⁻¹ = A := by rw [← hA', nineThree_conj_inv]
  have hA'inv : conjSubgroup A h'⁻¹ = V := by rw [← hV', nineThree_conj_inv]
  have hCV : conjSubgroup (nineSwapCV V A S) h'⁻¹ = nineSwapCA V A S :=
    conj_nineSwapCV hh'inv hV'inv hA'inv
  have hPsyl : IsSylowIn 2 (T ⊓ centralizer (A : Set G)) (nineSwapCA V A S) :=
    Nine3Core.isSylowIn_nineSwapCA h
  have hPS : T ⊓ centralizer (A : Set G) ≤ S := nine_three_four_centralizer h
  intro s hs
  rw [mem_conjSubgroup_iff]
  have hsS : s ∈ S := hs.1.1
  have hsCV : s ∈ centralizer (V : Set G) := hs.1.2
  have hsNA : s ∈ normalizer (A : Set G) := hs.2
  have hsStab : s ∈ nineSwapStab V A S :=
    ⟨⟨h.S_le_nineDeltaStab hsS, (h.leS.trans h.h9.sylow.le) hsS⟩, hsNA⟩
  have hsCV' : s ∈ nineSwapCV V A S := ⟨hsStab, hsCV⟩
  have htCA : h' * s * h'⁻¹ ∈ nineSwapCA V A S := by
    have hmem : h' * s * h'⁻¹ ∈ conjSubgroup (nineSwapCV V A S) h'⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have e : h'⁻¹ * (h' * s * h'⁻¹) * (h'⁻¹)⁻¹ = s := by group
      rw [e]
      exact hsCV'
    rwa [hCV] at hmem
  have htY : h' * s * h'⁻¹ ∈ Y := by
    have hmem : s ∈ conjSubgroup Y h' := by rw [hY']; exact hS0Y hs
    exact mem_conjSubgroup_iff.mp hmem
  have h2 : IsPGroup 2 (Y ⊓ nineSwapCA V A S : Subgroup G) := hY.isPGroup.to_le inf_le_left
  have hle : Y ⊓ nineSwapCA V A S ≤ T ⊓ centralizer (A : Set G) :=
    nineThree_le_of_isSylowIn hPsyl (le_inf hPY hPsyl.le) inf_le_right h2
  exact hPS (hle ⟨htY, htCA⟩)

theorem nine_three_exists_swap_sym (h : Nine3Core V T A K S X p) :
    ∃ g ∈ nineDeltaStab V S, conjSubgroup V g = A ∧ conjSubgroup A g = V ∧
      g * g ∈ normalizer (V : Set G) ∧
      S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G) ≤ conjSubgroup S g ∧
      S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G) ≤ conjSubgroup S g⁻¹ := by
  obtain ⟨Y, hY, hPS0Y⟩ := h.exists_isSylowIn_nineSwap
  obtain ⟨g, hg, hVg, hAg, hYg⟩ := h.exists_swap_normalizing hY
  have hgg : g * g ∈ normalizer (V : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← CFSG.Quasithin.conjSubgroup_conjSubgroup, hVg,
      hAg]
  have hYginv : conjSubgroup Y g⁻¹ = Y := by
    have hh := nineThree_conj_inv Y g
    rwa [hYg] at hh
  have hginv : g⁻¹ ∈ nineDeltaStab V S := Subgroup.inv_mem _ hg
  have hVginv : conjSubgroup V g⁻¹ = A := by rw [← hAg, nineThree_conj_inv]
  have hAginv : conjSubgroup A g⁻¹ = V := by rw [← hVg, nineThree_conj_inv]
  exact ⟨g, hg, hVg, hAg, hgg,
    nineThree_S0_le_conj_of_swap h hg hVg hAg hYg hY hPS0Y,
    nineThree_S0_le_conj_of_swap h hginv hVginv hAginv hYginv hY hPS0Y⟩

theorem Nine3Choice.inv (hc : Nine3Choice V T A K S X p g x)
    (hS : S ⊓ centralizer (V : Set G) ⊓ normalizer (A : Set G) ≤ conjSubgroup S g⁻¹) :
    Nine3Choice V T A K S X p g⁻¹ x := by
  refine ⟨hc.core, Subgroup.inv_mem _ hc.g_mem, ?_, ?_, ?_, hS, hc.x_mem, hc.x_gen⟩
  · rw [← hc.A_g, nineThree_conj_inv]
  · rw [← hc.V_g, nineThree_conj_inv]
  · have h : (g * g)⁻¹ ∈ normalizer (V : Set G) := Subgroup.inv_mem _ hc.g_sq
    simpa [mul_inv_rev] using h

theorem Nine3Core.exists_choice_sym (h763 : SevenSixThreeAbelian V)
    (h : Nine3Core V T A K S X p) :
    ∃ g x : G, Nine3Choice V T A K S X p g x ∧ Nine3Choice V T A K S X p g⁻¹ x := by
  obtain ⟨g, hg, hVg, hAg, hgg, hS, hS'⟩ := nine_three_exists_swap_sym h
  haveI : IsCyclic ↥X := nine_two_four h763 h.hyp7 h.rk_gt h.hyp
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := ↥X)
  have hx : X = Subgroup.zpowers (y : G) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hy ⟨z, hz⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exact Subgroup.zpowers_le.mpr y.2
  refine ⟨g, (y : G), ⟨h, hg, hVg, hAg, hgg, hS, y.2, hx⟩, ?_⟩
  exact Nine3Choice.inv ⟨h, hg, hVg, hAg, hgg, hS, y.2, hx⟩ hS'

theorem nine_H0_le_normalizer_sym
    (hN : nineH V K ≤ normalizer (nineI0 V K g : Set G))
    (hN' : nineH V K ≤ normalizer (nineI0 V K g⁻¹ : Set G)) :
    nineH0 V K g ≤ normalizer (nineI0 V K g : Set G) := by
  refine sup_le hN ?_
  have hI0 : conjSubgroup (nineI0 V K g⁻¹) g = nineI0 V K g := by
    unfold nineI0
    rw [nineThree_conj_sup, nineThree_conj_inv']
    exact sup_comm _ _
  have h := E3.conjSubgroup_mono_left g hN'
  rw [E3.conjSubgroup_normalizer, hI0] at h
  exact h

end CFSG.LocalAnalysis.WeakClosure81
