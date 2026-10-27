module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeEight

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private lemma nine3_sum_ite_smul {α M : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid M] [Module (ZMod 2) M] (f : α → M) (T : Finset α) :
    (∑ a : α, (if a ∈ T then (1 : ZMod 2) else 0) • f a) = ∑ a ∈ T, f a := by
  have h1 : (∑ a : α, (if a ∈ T then (1 : ZMod 2) else 0) • f a)
      = ∑ a : α, (if a ∈ T then f a else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a ∈ T <;> simp [ha]
  rw [h1, ← Finset.sum_filter (s := (Finset.univ : Finset α)) (p := fun a => a ∈ T)
    (f := f), Finset.filter_univ_mem]

private theorem nine3_list_prod_mem {W : Subgroup G} :
    ∀ {Ls : List (Subgroup G)} {bs : List G}, (∀ B ∈ Ls, B ≤ W) →
      List.Forall₂ (fun B b => b ∈ B) Ls bs → bs.prod ∈ W := by
  intro Ls
  induction Ls with
  | nil =>
    intro bs hle hb
    obtain rfl := List.forall₂_nil_left_iff.mp hb
    simp
  | cons B Ls' ih =>
    intro bs hle hb
    obtain ⟨b, bs', hbhead, hbtail, rfl⟩ := List.forall₂_cons_left_iff.mp hb
    exact W.mul_mem (hle B (by simp) hbhead)
      (ih (fun B' hB' => hle B' (List.mem_cons_of_mem B hB')) hbtail)

private theorem nine3_priv_main (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    (h3 : 3 ≤ Nat.card ↥(nineDelta V S)) :
    (∀ (Ls : List (Subgroup G)) (bs : List G), Ls.Nodup → Ls ≠ [] →
      (∀ B ∈ Ls, B ∈ nineOmegaIn V K S) →
      List.Forall₂ (fun B b => b ∈ B ∧ b ∉ pCoreOf 2 K) Ls bs →
      bs.prod ∉ nineW0 V K S g) ∧
    (nineZ V K S ⊓ nineW0 V K S g = ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) := by
  classical
  have hW : IsElemAbelian 2 (nineW V S) := hc.core.nineW_isElemAbelian
  have hW₀ : nineW0 V K S g ≤ nineW V S := hc.nineW0_le_nineW
  have hLW : nineL K A x g ≤ normalizer (nineW V S : Set G) := hc.nineL_le_normalizer_nineW
  have hLW₀ : nineL K A x g ≤ normalizer (nineW0 V K S g : Set G) :=
    hc.nineL_le_normalizer_nineW0 hI
  obtain ⟨M, _, _, ρ, π, hsurj, hker, hequiv⟩ := nineThree_exists_rep hW hW₀ hLW hLW₀
  haveI : Finite M := Finite.of_surjective π hsurj
  letI : Fintype ↥(nineDelta V S) := Fintype.ofFinite _
  let ι : ↥(nineL K A x g) →* ↥(nineDeltaStab V S) :=
    { toFun := fun l => ⟨l.1, hc.nineL_le_nineDeltaStab l.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let σ : ↥(nineL K A x g) →* Equiv.Perm ↥(nineDelta V S) := (nineDeltaPerm V S).comp ι
  have hσ : ∀ (l : ↥(nineL K A x g)) (B : ↥(nineDelta V S)),
      (σ l B).1 = conjSubgroup B.1 (l : G)⁻¹ := fun l B => rfl
  have hΔW : ∀ B ∈ nineDelta V S, B ≤ nineW V S := fun B hB => le_iSup₂_of_le B hB le_rfl
  have hidx : ∀ B ∈ nineDelta V S, (B ⊓ nineW0 V K S g).relIndex B = 2 :=
    fun B hB => hc.relIndex_inf_nineW0 hI hB
  have hnc : ∃ B ∈ nineDelta V S, ∃ B' ∈ nineDelta V S, ¬ B ≤ B' ⊔ nineW0 V K S g :=
    ⟨A, hc.core.A_mem_nineDelta, V, hc.core.V_mem_nineDelta, hc.not_A_le_sup hI⟩
  have hex : ∀ B : ↥(nineDelta V S), ∃ b : G, b ∈ B.1 ∧ b ∉ nineW0 V K S g := by
    intro B
    by_contra hcon
    push Not at hcon
    have h1 : (B.1 ⊓ nineW0 V K S g).relIndex B.1 = 1 :=
      Subgroup.relIndex_eq_one.2 (fun x hx => ⟨hx, hcon x hx⟩)
    rw [hidx B.1 B.2] at h1
    omega
  choose b hbB hbW using hex
  let m : ↥(nineDelta V S) → M := fun B =>
    π (Additive.ofMul ⟨b B, hΔW B.1 B.2 (hbB B)⟩)
  have huniq : ∀ (B : ↥(nineDelta V S)) (c : G) (hcB : c ∈ B.1) (hcW : c ∉ nineW0 V K S g),
      π (Additive.ofMul ⟨c, hΔW B.1 B.2 hcB⟩) = m B := by
    intro B c hcB hcW
    have hind : ((B.1 ⊓ nineW0 V K S g).subgroupOf B.1).index = 2 := hidx B.1 B.2
    have hx : (⟨b B, hbB B⟩⁻¹ : ↥B.1) ∉ (B.1 ⊓ nineW0 V K S g).subgroupOf B.1 := by
      intro h
      apply hbW B
      have h' : (b B)⁻¹ ∈ nineW0 V K S g := (h : ((b B)⁻¹ : G) ∈ B.1 ⊓ nineW0 V K S g).2
      simpa using (nineW0 V K S g).inv_mem h'
    have hy : (⟨c, hcB⟩ : ↥B.1) ∉ (B.1 ⊓ nineW0 V K S g).subgroupOf B.1 := fun h => hcW h.2
    have hxy := (Subgroup.mul_mem_iff_of_index_two hind).2 (iff_of_false hx hy)
    have hW0 : (b B)⁻¹ * c ∈ nineW0 V K S g := (hxy : (b B)⁻¹ * c ∈ B.1 ⊓ nineW0 V K S g).2
    have h1 : (⟨c, hΔW B.1 B.2 hcB⟩ : ↥(nineW V S)) =
        ⟨b B, hΔW B.1 B.2 (hbB B)⟩ *
          ⟨(b B)⁻¹ * c, hW₀ hW0⟩ := Subtype.ext (by simp)
    rw [h1, ofMul_mul, map_add, (hker ⟨(b B)⁻¹ * c, hW₀ hW0⟩).2 hW0, add_zero]
  have hm : ∀ (l : ↥(nineL K A x g)) (B : ↥(nineDelta V S)),
      (ρ l : M →ₗ[ZMod 2] M) (m B) = m (σ l B) := by
    intro l B
    have hcW' : (l : G) * b B * (l : G)⁻¹ ∈ nineW V S :=
      (Subgroup.mem_normalizer_iff.mp (hLW l.2) (b B)).mp (hΔW B.1 B.2 (hbB B))
    have hcB : (l : G) * b B * (l : G)⁻¹ ∈ (σ l B).1 := by
      rw [hσ, mem_conjSubgroup_iff]
      simpa [mul_assoc] using hbB B
    have hcW : (l : G) * b B * (l : G)⁻¹ ∉ nineW0 V K S g := by
      intro h
      exact hbW B ((Subgroup.mem_normalizer_iff.mp (hLW₀ l.2) (b B)).2 h)
    rw [← huniq (σ l B) _ hcB hcW]
    exact (hequiv l ⟨b B, hΔW B.1 B.2 (hbB B)⟩ ⟨_, hcW'⟩ rfl).symm
  have hspan : Submodule.span (ZMod 2) (Set.range m) = ⊤ := by
    let T : Subgroup ↥(nineW V S) :=
      { carrier := {w | π (Additive.ofMul w) ∈ Submodule.span (ZMod 2) (Set.range m)}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, ofMul_mul, map_add]
          exact Submodule.add_mem _ ha hb
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq, ofMul_inv, map_neg]
          exact Submodule.neg_mem _ ha }
    have hBT : ∀ B ∈ nineDelta V S, B ≤ T.map (nineW V S).subtype := by
      intro B hB x hx
      refine ⟨⟨x, hΔW B hB hx⟩, ?_, rfl⟩
      show π (Additive.ofMul ⟨x, hΔW B hB hx⟩) ∈ Submodule.span (ZMod 2) (Set.range m)
      by_cases hxW : x ∈ nineW0 V K S g
      · rw [(hker ⟨x, hΔW B hB hx⟩).2 hxW]
        exact Submodule.zero_mem _
      · rw [huniq ⟨B, hB⟩ x hx hxW]
        exact Submodule.subset_span ⟨⟨B, hB⟩, rfl⟩
    have hWT : nineW V S ≤ T.map (nineW V S).subtype := by
      have h := iSup₂_le (f := fun B (_ : B ∈ nineDelta V S) => B) hBT
      rwa [show (⨆ B ∈ nineDelta V S, B) = nineW V S from rfl] at h
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, rfl⟩ := hsurj v
    obtain ⟨t, ht, htw⟩ := hWT (Additive.toMul w).2
    have : t = Additive.toMul w := Subtype.ext htw
    rw [this] at ht
    exact ht
  have hne : ∃ a b : ↥(nineDelta V S), m a ≠ m b := by
    obtain ⟨B, hB, B', hB', hnot⟩ := hnc
    refine ⟨⟨B, hB⟩, ⟨B', hB'⟩, fun heq => hnot ?_⟩
    intro x hx
    by_cases hxW : x ∈ nineW0 V K S g
    · exact Subgroup.mem_sup_right hxW
    · have h1 := huniq ⟨B, hB⟩ x hx hxW
      have h2 : π (Additive.ofMul ⟨x, hΔW B hB hx⟩) =
          π (Additive.ofMul ⟨b ⟨B', hB'⟩, hΔW B' hB' (hbB ⟨B', hB'⟩)⟩) := h1.trans heq
      have h3 : x * (b ⟨B', hB'⟩)⁻¹ ∈ nineW0 V K S g := by
        have hxW' : (⟨x, hΔW B hB hx⟩ : ↥(nineW V S)) *
            (⟨b ⟨B', hB'⟩, hΔW B' hB' (hbB ⟨B', hB'⟩)⟩ : ↥(nineW V S))⁻¹ =
            ⟨x * (b ⟨B', hB'⟩)⁻¹,
              (nineW V S).mul_mem (hΔW B hB hx)
                ((nineW V S).inv_mem (hΔW B' hB' (hbB ⟨B', hB'⟩)))⟩ := rfl
        have := (hker ((⟨x, hΔW B hB hx⟩ : ↥(nineW V S)) *
            (⟨b ⟨B', hB'⟩, hΔW B' hB' (hbB ⟨B', hB'⟩)⟩ : ↥(nineW V S))⁻¹)).1 (by
          rw [ofMul_mul, ofMul_inv, map_add, map_neg, h2, add_neg_cancel])
        exact this
      have : x = (x * (b ⟨B', hB'⟩)⁻¹) * b ⟨B', hB'⟩ := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h3)
        (Subgroup.mem_sup_left (hbB ⟨B', hB'⟩))
  let φ : (↥(nineDelta V S) → ZMod 2) →ₗ[ZMod 2] M := Fintype.linearCombination (ZMod 2) m
  have hsurjφ : Function.Surjective φ :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination (ZMod 2) m).1 hspan
  have hφ : ∀ (γ : ↥(nineL K A x g)) (f : ↥(nineDelta V S) → ZMod 2),
      φ (fun ω => f ((σ γ).symm ω)) = (ρ γ : M →ₗ[ZMod 2] M) (φ f) := by
    intro γ f
    simp only [φ, Fintype.linearCombination_apply, map_sum, map_smul, hm]
    have := Equiv.sum_comp (σ γ) (fun i => f ((σ γ).symm i) • m i)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hKinv : ∀ γ : ↥(nineL K A x g), ∀ f ∈ LinearMap.ker φ,
      (fun ω => f ((σ γ).symm ω)) ∈ LinearMap.ker φ := by
    intro γ f hf
    rw [LinearMap.mem_ker] at hf ⊢
    rw [hφ, hf, map_zero]
  haveI : Nonempty ↥(nineDelta V S) :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card ↥(nineDelta V S) by omega)).1
  have hodd : Odd (Fintype.card ↥(nineDelta V S)) := by
    rw [← Nat.card_eq_fintype_card]
    exact hc.odd_card_nineDelta h3
  have htrans : ∀ a b : ↥(nineDelta V S), ∃ γ : ↥(nineL K A x g), σ γ a = b := by
    intro a b
    obtain ⟨l, hl, hlab⟩ := hc.nineL_transitive h3 a.1 a.2 b.1 b.2
    exact ⟨⟨l⁻¹, (nineL K A x g).inv_mem hl⟩, Subtype.ext (by
      rw [hσ, inv_inv]
      exact hlab)⟩
  let v : ↥(nineDelta V S) := ⟨V, hc.core.V_mem_nineDelta⟩
  let Q : Subgroup ↥(nineL K A x g) := (nineD K A x).subgroupOf (nineL K A x g)
  have hQ : IsPGroup 2 Q := (hc.core.nineD_isElemAbelian hc.x_mem).isPGroup.comap_subtype
  have hQv : ∀ q ∈ Q, σ q v = v := by
    intro q hq
    apply Subtype.ext
    rw [hσ]
    exact hc.conjSubgroup_V_of_mem_nineD ((nineD K A x).inv_mem hq)
  have hQt : ∀ a b : ↥(nineDelta V S), a ≠ v → b ≠ v → ∃ q ∈ Q, σ q a = b := by
    intro a b ha hb
    obtain ⟨d, hd, hdab⟩ := hc.nineD_transitive_delta (B := a.1) (B' := b.1) a.2 b.2
      (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
    refine ⟨⟨d⁻¹, (nineL K A x g).inv_mem (Subgroup.mem_sup_left hd)⟩, ?_, Subtype.ext ?_⟩
    · exact (nineD K A x).inv_mem hd
    · rw [hσ, inv_inv]
      exact hdab
  obtain ⟨a, b, hab⟩ := hne
  have hab' : a ≠ b := fun h => hab (congrArg m h)
  have hP : (Pi.single a 1 + Pi.single b 1 : ↥(nineDelta V S) → ZMod 2) ∈
      nineThreeEven ↥(nineDelta V S) := by
    show ∑ ω, (Pi.single a 1 + Pi.single b 1 : ↥(nineDelta V S) → ZMod 2) ω = 0
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp
    decide
  have hnotK : (Pi.single a 1 + Pi.single b 1 : ↥(nineDelta V S) → ZMod 2) ∉
      LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_add, Fintype.linearCombination_apply_single,
      Fintype.linearCombination_apply_single, one_smul, one_smul]
    intro h
    exact hab ((eq_neg_of_add_eq_zero_left h).trans (ZModModule.neg_eq_self _))
  have hK : LinearMap.ker φ = ⊥ ∨ LinearMap.ker φ = nineThreeConst ↥(nineDelta V S) := by
    rcases nineThree_perm_trichotomy σ hodd htrans v Q hQ hQt _ hKinv with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (by rw [h]; exact hP) hnotK
    · exact absurd (by rw [h]; exact Submodule.mem_top) hnotK
  let m' : Subgroup G → M := fun B => if hB : B ∈ nineDelta V S then m ⟨B, hB⟩ else 0
  have hm'_mem : ∀ (B : Subgroup G) (hB : B ∈ nineDelta V S), m' B = m ⟨B, hB⟩ := by
    intro B hB
    simp only [m', dif_pos hB]
  have huniq' : ∀ (B : Subgroup G) (hB : B ∈ nineDelta V S) (c : G) (hcB : c ∈ B),
      c ∉ nineW0 V K S g →
      π (Additive.ofMul ⟨c, (hΔW B hB) hcB⟩) = m' B := by
    intro B hB c hcB hcW
    rw [hm'_mem B hB]
    exact huniq ⟨B, hB⟩ c hcB hcW
  have hsumΔ : ∀ T : Finset ↥(nineDelta V S), T.Nonempty → T ≠ Finset.univ →
      (∑ B ∈ T, m B) ≠ 0 := by
    intro T hTne hTuniv hzero
    let g : ↥(nineDelta V S) → ZMod 2 := fun B => if B ∈ T then 1 else 0
    have hφg : φ g = ∑ B ∈ T, m B := by
      rw [show φ g = ∑ B : ↥(nineDelta V S), g B • m B from
        Fintype.linearCombination_apply (R := ZMod 2) (v := m) g]
      simp only [g]
      exact nine3_sum_ite_smul m T
    have hgker : g ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, hφg, hzero]
    rcases hK with hbot | hconst
    · rw [hbot, Submodule.mem_bot] at hgker
      obtain ⟨B, hB⟩ := hTne
      have h1 : g B = 0 := congrFun hgker B
      rw [show g B = 1 by simp [g, hB]] at h1
      exact one_ne_zero h1
    · rw [hconst] at hgker
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgker
      obtain ⟨B, hB⟩ := hTne
      obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ ∉ T := by
        by_contra h
        exact hTuniv (Finset.eq_univ_iff_forall.mpr (fun B => by
          by_contra hB
          exact h ⟨B, hB⟩))
      have hcB : g B = c := by
        have h := congrFun hc B
        simpa [Pi.smul_apply, smul_eq_mul] using h.symm
      have hcB₀ : g B₀ = c := by
        have h := congrFun hc B₀
        simpa [Pi.smul_apply, smul_eq_mul] using h.symm
      have hB1 : g B = 1 := by simp [g, hB]
      have hB0 : g B₀ = 0 := by simp [g, hB₀]
      exact one_ne_zero (by rw [← hB1, hcB, ← hcB₀, hB0])
  have hsum' : ∀ T : Finset (Subgroup G), (∀ B ∈ T, B ∈ nineDelta V S) → T.Nonempty →
      V ∉ T → (∑ B ∈ T, m' B) ≠ 0 := by
    intro T hT hTne hTV hzero
    let emb : {B // B ∈ T} ↪ ↥(nineDelta V S) :=
      { toFun := fun B => ⟨B.1, hT B.1 B.2⟩
        inj' := fun B₁ B₂ h =>
          Subtype.ext (congrArg (fun B : ↥(nineDelta V S) => (B : Subgroup G)) h) }
    have hsum1 : (∑ B ∈ T, m' B) = ∑ B ∈ T.attach.map emb, m B := by
      rw [← Finset.sum_attach T m', Finset.sum_map]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact hm'_mem x.1 (hT x.1 x.2)
    have hT'ne : (T.attach.map emb).Nonempty := by
      obtain ⟨B, hB⟩ := hTne
      exact ⟨emb ⟨B, hB⟩, Finset.mem_map.mpr
        ⟨⟨B, hB⟩, Finset.mem_attach T ⟨B, hB⟩, rfl⟩⟩
    have hTV' : (⟨V, hc.core.V_mem_nineDelta⟩ : ↥(nineDelta V S)) ∉ T.attach.map emb := by
      intro hmem
      obtain ⟨x, -, hx⟩ := Finset.mem_map.mp hmem
      have hxval : (emb x : Subgroup G) = V := Subtype.ext_iff.mp hx
      exact hTV (by rw [← hxval]; exact x.2)
    have hT'univ : T.attach.map emb ≠ Finset.univ := by
      intro h
      exact hTV' (h ▸ Finset.mem_univ _)
    exact hsumΔ (T.attach.map emb) hT'ne hT'univ (by rw [← hsum1]; exact hzero)
  have hprod : ∀ (Ls : List (Subgroup G)) (bs : List G),
      (∀ B ∈ Ls, B ∈ nineOmegaIn V K S) →
      List.Forall₂ (fun B b => b ∈ B ∧ b ∉ pCoreOf 2 K) Ls bs → Ls.Nodup →
      ∀ (hW : bs.prod ∈ nineW V S),
      π (Additive.ofMul ⟨bs.prod, hW⟩) = ∑ B ∈ Ls.toFinset, m' B := by
    intro Ls
    induction Ls with
    | nil =>
      intro bs hmem hb hLs hW
      obtain rfl := List.forall₂_nil_left_iff.mp hb
      simpa using (hker ⟨[].prod, hW⟩).2 (nineW0 V K S g).one_mem
    | cons B Ls' ih =>
      intro bs hmem hb hLs hW
      obtain ⟨b, bs', hbhead, hbtail, rfl⟩ := List.forall₂_cons_left_iff.mp hb
      have hBΩ : B ∈ nineOmegaIn V K S := hmem B (by simp)
      have hBΔ : B ∈ nineDelta V S := hc.core.mem_nineDelta_iff.mpr (Or.inr hBΩ)
      have hbW0 : b ∉ nineW0 V K S g := by
        intro hb0
        have hbR : b ∈ B ⊓ pCoreOf 2 K := by
          rw [← hc.inf_nineW0_of_mem hBΩ]
          exact Subgroup.mem_inf.mpr ⟨hbhead.1, hb0⟩
        exact hbhead.2 hbR.2
      have hbW : b ∈ nineW V S := hΔW B hBΔ hbhead.1
      have hmem' : ∀ B' ∈ Ls', B' ∈ nineOmegaIn V K S :=
        fun B' hB' => hmem B' (List.mem_cons_of_mem B hB')
      have hnodup' : Ls'.Nodup := (List.nodup_cons.mp hLs).2
      have hBnotMem : B ∉ Ls'.toFinset := by
        intro hmemT
        exact (List.nodup_cons.mp hLs).1 (List.mem_toFinset.mp hmemT)
      have hbsW : bs'.prod ∈ nineW V S :=
        nine3_list_prod_mem (W := nineW V S)
          (fun B' hB' => hΔW B' (hc.core.mem_nineDelta_iff.mpr (Or.inr (hmem' B' hB'))))
          (hbtail.imp (fun _ _ h => h.1))
      have hmul : (⟨(b :: bs').prod, hW⟩ : ↥(nineW V S)) =
          ⟨b, hbW⟩ * ⟨bs'.prod, hbsW⟩ := Subtype.ext (by simp [List.prod_cons])
      rw [hmul, ofMul_mul, map_add, huniq' B hBΔ b hbhead.1 hbW0,
        ih bs' hmem' hbtail hnodup' hbsW, List.toFinset_cons,
        Finset.sum_insert hBnotMem]
  constructor
  · intro Ls bs hLs hne hmem hb hmemW0
    have hbsW : bs.prod ∈ nineW V S :=
      nine3_list_prod_mem (W := nineW V S)
        (fun B hB => hΔW B (hc.core.mem_nineDelta_iff.mpr (Or.inr (hmem B hB))))
        (hb.imp (fun _ _ h => h.1))
    have hπ := hprod Ls bs hmem hb hLs hbsW
    have hzero : (∑ B ∈ Ls.toFinset, m' B) = 0 := by
      rw [← hπ]
      exact (hker ⟨bs.prod, hbsW⟩).2 hmemW0
    have hT : ∀ B ∈ Ls.toFinset, B ∈ nineDelta V S := fun B hB =>
      hc.core.mem_nineDelta_iff.mpr (Or.inr (hmem B (List.mem_toFinset.mp hB)))
    have hTne : Ls.toFinset.Nonempty := by
      have hpos : 0 < Ls.length := List.length_pos_iff.mpr hne
      have hcard : 0 < (Ls.toFinset).card := by
        rw [List.toFinset_card_of_nodup hLs]; exact hpos
      exact Finset.card_pos.mp hcard
    have hTV : V ∉ Ls.toFinset := fun hV =>
      hc.core.V_not_mem_nineOmegaIn (hmem V (List.mem_toFinset.mp hV))
    exact (hsum' Ls.toFinset hT hTne hTV) hzero
  · haveI : Fintype ↥(nineOmegaIn V K S) := Fintype.ofFinite _
    letI : CommGroup ↥(nineW V S) :=
      @IsMulCommutative.instCommGroup _ _ hc.core.nineW_isElemAbelian.1
    haveI : Module (ZMod 2) (Additive ↥(nineW V S)) :=
      AddCommGroup.zmodModule (fun x => by
        rw [two_nsmul, ← ofMul_toMul x, ← ofMul_mul,
          show Additive.toMul x * Additive.toMul x = 1 by
            rw [← pow_two]
            exact Subtype.ext (hW.2 _ (Additive.toMul x).2),
          ofMul_one])
    have hZW : nineZ V K S ≤ nineW V S := by
      rw [hc.core.nineW_eq]
      exact le_sup_right
    let J : Subgroup G := ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K
    have hJZ : J ≤ nineZ V K S := by
      refine iSup₂_le fun B hB => ?_
      exact (inf_le_left : B ⊓ pCoreOf 2 K ≤ B).trans (le_iSup₂_of_le B hB le_rfl)
    have hJW : J ≤ nineW V S := hJZ.trans hZW
    have hJW0 : J ≤ nineW0 V K S g := le_sup_right
    have hZmem : ∀ (B : ↥(nineOmegaIn V K S)) {x : G}, x ∈ B.1 → x ∈ nineZ V K S := by
      intro B x hx
      have h1 : x ∈ (⨆ _ : B.1 ∈ nineOmegaIn V K S, B.1) :=
        Subgroup.mem_iSup_of_mem (S := fun _ : B.1 ∈ nineOmegaIn V K S => B.1) B.2 hx
      exact Subgroup.mem_iSup_of_mem (S := fun B : Subgroup G =>
        ⨆ _ : B ∈ nineOmegaIn V K S, B) B.1 h1
    have hJmem : ∀ (B : ↥(nineOmegaIn V K S)) {x : G},
        x ∈ B.1 ⊓ pCoreOf 2 K → x ∈ J := by
      intro B x hx
      show x ∈ (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K)
      have h1 : x ∈ (⨆ _ : B.1 ∈ nineOmegaIn V K S, B.1 ⊓ pCoreOf 2 K) :=
        Subgroup.mem_iSup_of_mem
          (S := fun _ : B.1 ∈ nineOmegaIn V K S => B.1 ⊓ pCoreOf 2 K) B.2 hx
      exact Subgroup.mem_iSup_of_mem (S := fun B : Subgroup G =>
        ⨆ _ : B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) B.1 h1
    have hex : ∀ B : ↥(nineOmegaIn V K S), ∃ b : G, b ∈ B.1 ∧ b ∉ pCoreOf 2 K :=
      fun B => hc.core.exists_not_mem_pCoreOf B.2
    choose β hβB hβR using hex
    have hβW : ∀ B : ↥(nineOmegaIn V K S), β B ∈ nineW V S := fun B =>
      hΔW B.1 (hc.core.mem_nineDelta_iff.mpr (Or.inr B.2)) (hβB B)
    have hβW0 : ∀ B : ↥(nineOmegaIn V K S), β B ∉ nineW0 V K S g := by
      intro B hβ0
      have hβR' : β B ∈ B.1 ⊓ pCoreOf 2 K := by
        rw [← hc.inf_nineW0_of_mem B.2]
        exact Subgroup.mem_inf.mpr ⟨hβB B, hβ0⟩
      exact hβR B hβR'.2
    let f : ↥(nineOmegaIn V K S) → Additive ↥(nineW V S) :=
      fun B => Additive.ofMul ⟨β B, hβW B⟩
    have hπf : ∀ B : ↥(nineOmegaIn V K S),
        π (f B) = m' B.1 := fun B =>
      huniq' B.1 (hc.core.mem_nineDelta_iff.mpr (Or.inr B.2)) (β B) (hβB B) (hβW0 B)
    have hindep : ∀ c : ↥(nineOmegaIn V K S) → ZMod 2,
        Fintype.linearCombination (ZMod 2) (fun B : ↥(nineOmegaIn V K S) => m' B.1) c = 0 →
        c = 0 := by
      intro c hc0
      let T : Finset ↥(nineOmegaIn V K S) := Finset.univ.filter (fun B => c B ≠ 0)
      have hc_ind : ∀ B, c B = if B ∈ T then (1 : ZMod 2) else 0 := by
        intro B
        by_cases hB : B ∈ T
        · simp only [hB, if_true]
          have hcB : c B ≠ 0 := (Finset.mem_filter.mp hB).2
          have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
          exact (h2 (c B)).resolve_left hcB
        · simp only [hB, if_false]
          by_contra h
          exact hB (Finset.mem_filter.mpr ⟨Finset.mem_univ B, h⟩)
      have hsum_eq0 : Fintype.linearCombination (ZMod 2)
          (fun B : ↥(nineOmegaIn V K S) => m' B.1) c = ∑ B ∈ T, m' B.1 := by
        rw [Fintype.linearCombination_apply]
        simp only [hc_ind]
        exact nine3_sum_ite_smul (fun B : ↥(nineOmegaIn V K S) => m' B.1) T
      have hsum_eq : (∑ B ∈ T, m' B.1) = 0 := hsum_eq0 ▸ hc0
      have hTempty : T.image (fun B : ↥(nineOmegaIn V K S) => B.1) = ∅ := by
        by_contra hne
        have hne' : (T.image (fun B : ↥(nineOmegaIn V K S) => B.1)).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hne
        have hall : ∀ B ∈ T.image (fun B : ↥(nineOmegaIn V K S) => B.1),
            B ∈ nineDelta V S := by
          intro B hB
          obtain ⟨B₀, -, rfl⟩ := Finset.mem_image.mp hB
          exact hc.core.mem_nineDelta_iff.mpr (Or.inr B₀.2)
        have hV : V ∉ T.image (fun B : ↥(nineOmegaIn V K S) => B.1) := by
          intro hV
          obtain ⟨B₀, -, hB₀⟩ := Finset.mem_image.mp hV
          exact hc.core.V_not_mem_nineOmegaIn (by simpa [hB₀] using B₀.2)
        exact hsum' (T.image (fun B : ↥(nineOmegaIn V K S) => B.1)) hall hne' hV (by
          rw [Finset.sum_image (by
            intro B₁ _ B₂ _ h
            exact Subtype.ext h)]
          exact hsum_eq)
      have hTempty' : T = ∅ := Finset.image_eq_empty.mp hTempty
      funext B
      by_contra hcB
      have hB : B ∉ T := by rw [hTempty']; exact Finset.notMem_empty B
      exact hB (Finset.mem_filter.mpr ⟨Finset.mem_univ B, hcB⟩)
    have hdecomp : ∀ z ∈ nineZ V K S, ∃ j, ∃ (hj : j ∈ J),
        ∃ c : ↥(nineOmegaIn V K S) → ZMod 2, ∀ (hzW : z ∈ nineW V S),
        Additive.ofMul (⟨z, hzW⟩ : ↥(nineW V S)) =
          Additive.ofMul (⟨j, hJW hj⟩ : ↥(nineW V S)) +
            Fintype.linearCombination (ZMod 2) f c := by
      have hZeq : nineZ V K S = ⨆ B : ↥(nineOmegaIn V K S), B.1 :=
        (iSup_subtype'' (nineOmegaIn V K S) (fun B : Subgroup G => B)).symm
      intro z hz
      rw [hZeq] at hz
      refine (Subgroup.iSup_induction (fun B : ↥(nineOmegaIn V K S) => B.1)
        (C := fun z => z ∈ nineZ V K S ∧ ∃ j, ∃ (hj : j ∈ J),
          ∃ c : ↥(nineOmegaIn V K S) → ZMod 2, ∀ (hzW : z ∈ nineW V S),
          Additive.ofMul (⟨z, hzW⟩ : ↥(nineW V S)) =
            Additive.ofMul (⟨j, hJW hj⟩ : ↥(nineW V S)) +
              Fintype.linearCombination (ZMod 2) f c) hz ?_ ?_ ?_).2
      · intro B z hzB
        refine ⟨hZmem B hzB, ?_⟩
        by_cases hzR : z ∈ pCoreOf 2 K
        · exact ⟨z, hJmem B (Subgroup.mem_inf.mpr ⟨hzB, hzR⟩), 0, fun hzW => by simp⟩
        · have hj : (β B)⁻¹ * z ∈ J :=
            hJmem B (Subgroup.mem_inf.mpr ⟨B.1.mul_mem (B.1.inv_mem (hβB B)) hzB,
              hc.core.nineOmegaIn_inv_mul_mem B.2 (hβB B) hzB (hβR B) hzR⟩)
          refine ⟨(β B)⁻¹ * z, hj, Pi.single B 1, fun hzW => ?_⟩
          have hz_eq : (⟨z, hzW⟩ : ↥(nineW V S)) =
              ⟨(β B)⁻¹ * z, hJW hj⟩ * ⟨β B, hβW B⟩ := by
            refine Subtype.ext ?_
            show z = (β B)⁻¹ * z * β B
            rw [mul_assoc, hc.core.nineW_mul_comm hzW (hβW B), inv_mul_cancel_left]
          rw [hz_eq, ofMul_mul]
          congr 1
          rw [Fintype.linearCombination_apply_single, one_smul]
      · exact ⟨Subgroup.one_mem _, 1, J.one_mem, 0, fun hzW => by simp⟩
      · intro x y hx hy
        obtain ⟨hxZ, j₁, hj₁, c₁, hx_eq⟩ := hx
        obtain ⟨hyZ, j₂, hj₂, c₂, hy_eq⟩ := hy
        refine ⟨nineZ V K S |>.mul_mem hxZ hyZ, j₁ * j₂, J.mul_mem hj₁ hj₂, c₁ + c₂,
          fun hxyW => ?_⟩
        have hxW : x ∈ nineW V S := hZW hxZ
        have hyW : y ∈ nineW V S := hZW hyZ
        rw [show (⟨x * y, hxyW⟩ : ↥(nineW V S)) = ⟨x, hxW⟩ * ⟨y, hyW⟩ from
            Subtype.ext rfl,
          ofMul_mul, hx_eq hxW, hy_eq hyW,
          show (⟨j₁ * j₂, hJW (J.mul_mem hj₁ hj₂)⟩ : ↥(nineW V S)) =
            ⟨j₁, hJW hj₁⟩ * ⟨j₂, hJW hj₂⟩ from Subtype.ext rfl,
          ofMul_mul, map_add]
        abel
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzZ, hzW0⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨j, hj, c, hc_eq⟩ := hdecomp z hzZ
      have hzW : z ∈ nineW V S := hZW hzZ
      have hjW : j ∈ nineW V S := hJW hj
      have hπz : π (Additive.ofMul ⟨z, hzW⟩) = 0 := (hker ⟨z, hzW⟩).2 hzW0
      have hπj : π (Additive.ofMul ⟨j, hjW⟩) = 0 := (hker ⟨j, hjW⟩).2 (hJW0 hj)
      have hπF : ∀ c, π (Fintype.linearCombination (ZMod 2) f c) =
          Fintype.linearCombination (ZMod 2) (fun B : ↥(nineOmegaIn V K S) => m' B.1) c := by
        intro c
        rw [Fintype.linearCombination_apply, map_sum, Fintype.linearCombination_apply]
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [ZMod.map_smul, hπf]
      have hsum0 : Fintype.linearCombination (ZMod 2)
          (fun B : ↥(nineOmegaIn V K S) => m' B.1) c = 0 := by
        have h1 := congrArg π (hc_eq hzW)
        rw [hπz, map_add, hπj, hπF] at h1
        simpa using h1.symm
      have hc0 : c = 0 := hindep c hsum0
      have hz_eq_j : z = j := by
        have h := hc_eq hzW
        rw [hc0, map_zero, add_zero] at h
        have hsub : (⟨z, hzW⟩ : ↥(nineW V S)) = ⟨j, hjW⟩ := by
          have := congrArg Additive.toMul h
          simpa using this
        exact congrArg Subtype.val hsub
      rw [hz_eq_j]
      exact hj
    · exact le_inf (fun j hj => hJZ hj) hJW0
theorem nine3_prod_notMem_nineW0 (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    (h3 : 3 ≤ Nat.card ↥(nineDelta V S)) {Ls : List (Subgroup G)} {bs : List G}
    (hLs : Ls.Nodup) (hne : Ls ≠ []) (hmem : ∀ B ∈ Ls, B ∈ nineOmegaIn V K S)
    (hb : List.Forall₂ (fun B b => b ∈ B ∧ b ∉ pCoreOf 2 K) Ls bs) :
    bs.prod ∉ nineW0 V K S g :=
  (nine3_priv_main hc hI h3).1 Ls bs hLs hne hmem hb

end CFSG.LocalAnalysis.WeakClosure81
