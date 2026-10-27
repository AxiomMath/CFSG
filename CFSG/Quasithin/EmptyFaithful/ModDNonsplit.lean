module

public import CFSG.Quasithin.EmptyFaithful.ModDSetup
public import CFSG.Quasithin.EmptyFaithful.ModDLift

public section

namespace CFSG.Quasithin.ModD

open CFSG.CosetTable CFSG.Quasithin

section Quotient

variable {Γ U : Type*} [Group Γ] [CommGroup U]

@[expose] noncomputable def actQ (φ : Γ →* MulAut U) (Z : Subgroup U) (hZ : ∀ g : Γ, ∀ ζ ∈ Z, φ g ζ = ζ) :
    Γ →* MulAut (U ⧸ Z) where
  toFun g := QuotientGroup.congr Z Z (φ g) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show φ g y ∈ Z
      rw [hZ g y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hZ g x hx⟩)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]
  map_mul' := by
    intro g h
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]

theorem actQ_mk (φ : Γ →* MulAut U) (Z : Subgroup U) (hZ : ∀ g : Γ, ∀ ζ ∈ Z, φ g ζ = ζ) (g : Γ) (x : U) :
    actQ φ Z hZ g (QuotientGroup.mk x) = QuotientGroup.mk (φ g x) := rfl

end Quotient


section Main

variable
  {U : Type} [CommGroup U] [Finite U]

theorem A_preserves (g : U33G) (hg : g ∈ u33Data.A) (i : Fin 63) : vHom g i ∈ cSet ↔ i ∈ cSet := by
  let S : Subgroup U33G :=
    { carrier := {g | ∀ i : Fin 63, vHom g i ∈ cSet ↔ i ∈ cSet}
      mul_mem' := by
        intro a b ha hb i
        show vHom (a * b) i ∈ cSet ↔ i ∈ cSet
        rw [map_mul, Equiv.Perm.mul_apply]
        exact (ha _).trans (hb i)
      one_mem' := by
        intro i
        show vHom 1 i ∈ cSet ↔ i ∈ cSet
        rw [map_one]
        exact Iff.rfl
      inv_mem' := by
        intro a ha i
        show vHom a⁻¹ i ∈ cSet ↔ i ∈ cSet
        have h1 := ha (vHom a⁻¹ i)
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h1
        exact h1.symm }
  have hA : u33Data.A ≤ S := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg i
    have key : ∀ k : Fin 5, k ∈ [(0 : Fin 5), 1, 2, 3] → ∀ i : Fin 63, vHom (u33GenPG k.val) i ∈ cSet ↔ i ∈ cSet := by
      intro k hk i
      rw [vHom_gen]
      exact A_preserves_cSet k hk i
    rcases hg with rfl | rfl | rfl | rfl
    · exact key 0 (by simp) i
    · exact key 1 (by simp) i
    · exact key 2 (by simp) i
    · exact key 3 (by simp) i
  exact hA hg i


theorem pencil_bound (hsq : ∀ a : U, a * a = 1) (φ : U33G →* MulAut U) (Z : Subgroup U)
    (hZ : ∀ g : U33G, ∀ ζ ∈ Z, φ g ζ = ζ) (hcard : Nat.card (U ⧸ Z) = 2 ^ 6)
    (hirr : ∀ N : Subgroup U, Z ≤ N → (∀ g : U33G, ∀ n ∈ N, φ g n ∈ N) → N = Z ∨ N = ⊤)
    {z : U} (hz : z ∉ Z) (hzT : ∀ g ∈ u33Data.T, φ g z = z)
    {V : Subgroup U} (hzV : z ∈ V) (hV4 : Nat.card V = 4) (hVZ : V ⊓ Z = ⊥)
    {Y₁ Y₂ : Subgroup U33G} (hY₁T : u33Data.T ≤ Y₁) (hY₂T : u33Data.T ≤ Y₂)
    (hY₁1 : Y₁ ≠ u33Data.T) (hY₁2 : Y₁ ≠ ⊤) (hY₂1 : Y₂ ≠ u33Data.T) (hY₂2 : Y₂ ≠ ⊤) (hY : Y₁ ≠ Y₂)
    (hzY : ∀ g ∈ Y₂, φ g z = z) (hV : ∀ g ∈ Y₁, ∀ v ∈ V, φ g v ∈ V) :
    Nat.card (Subgroup.closure {m : U | ∃ g ∈ Y₂, ∃ v ∈ V, m = φ g v}) ≤ 8 := by
  classical
  let φ' : U33G →* MulAut (U ⧸ Z) := actQ φ Z hZ
  have hφ' : ∀ g x, φ' g (QuotientGroup.mk x) = QuotientGroup.mk (φ g x) := fun g x => actQ_mk φ Z hZ g x
  have hsq' : ∀ a : U ⧸ Z, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, hsq x]
      rfl
  have hirr' : ∀ N : Subgroup (U ⧸ Z), (∀ g : U33G, ∀ n ∈ N, φ' g n ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    let N' : Subgroup U := N.comap (QuotientGroup.mk' Z)
    have hZN : Z ≤ N' := by
      intro x hx
      show (QuotientGroup.mk x : U ⧸ Z) ∈ N
      rw [(QuotientGroup.eq_one_iff x).2 hx]
      exact N.one_mem
    have hinv : ∀ g : U33G, ∀ n ∈ N', φ g n ∈ N' := by
      intro g n hn
      show (QuotientGroup.mk (φ g n) : U ⧸ Z) ∈ N
      rw [← hφ']
      exact hN g _ hn
    rcases hirr N' hZN hinv with h | h
    · left
      refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      have hu : u ∈ N' := hx
      rw [h] at hu
      exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff u).2 hu)
    · right
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      have hu : u ∈ N' := by rw [h]; trivial
      exact hu
  have hinjV : ∀ a ∈ V, ∀ b ∈ V, (QuotientGroup.mk a : U ⧸ Z) = QuotientGroup.mk b → a = b := by
    intro a ha b hb h
    have h1 : a⁻¹ * b ∈ Z := QuotientGroup.eq.1 h
    have h2 : a⁻¹ * b ∈ V := V.mul_mem (V.inv_mem ha) hb
    have h3 : a⁻¹ * b ∈ V ⊓ Z := ⟨h2, h1⟩
    rw [hVZ] at h3
    exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 h3)
  have hV4' : Nat.card ↥(V.map (QuotientGroup.mk' Z)) = 4 := by
    have h1 : Nat.card ↥(V.map (QuotientGroup.mk' Z)) = Nat.card V := by
      symm
      refine Nat.card_congr (Equiv.ofBijective
        (fun v : V => (⟨QuotientGroup.mk' Z v, v, v.2, rfl⟩ : ↥(V.map (QuotientGroup.mk' Z)))) ⟨?_, ?_⟩)
      · intro a b h
        have h' : (QuotientGroup.mk (a : U) : U ⧸ Z) = QuotientGroup.mk (b : U) := congrArg Subtype.val h
        exact Subtype.ext (hinjV a a.2 b b.2 h')
      · rintro ⟨x, v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩
    rw [h1]
    exact hV4
  have hz' : (QuotientGroup.mk z : U ⧸ Z) ≠ 1 := fun h => hz ((QuotientGroup.eq_one_iff z).1 h)
  have hz2' : (QuotientGroup.mk z : U ⧸ Z) ^ 2 = 1 := by
    rw [pow_two]
    exact hsq' _
  have hzT' : ∀ g ∈ u33Data.T, φ' g (QuotientGroup.mk z) = QuotientGroup.mk z := by
    intro g hg
    rw [hφ', hzT g hg]
  have hzV' : (QuotientGroup.mk z : U ⧸ Z) ∈ V.map (QuotientGroup.mk' Z) := ⟨z, hzV, rfl⟩
  have hV' : ∀ g ∈ Y₁, ∀ v ∈ V.map (QuotientGroup.mk' Z), φ' g v ∈ V.map (QuotientGroup.mk' Z) := by
    rintro g hg _ ⟨v, hv, rfl⟩
    refine ⟨φ g v, hV g hg v hv, ?_⟩
    show (QuotientGroup.mk (φ g v) : U ⧸ Z) = φ' g (QuotientGroup.mk v)
    rw [hφ']
  obtain ⟨hY1B, hY2A, ε, m₁, m₂, hε1, hε2, hε3, horb, -⟩ :=
    pencil_setup hcard φ' hirr' hz' hz2' hzT' hzV' hV4' hY₁T hY₂T hY₁1 hY₁2 hY₂1 hY₂2 hY hV'
  have hzA : ∀ g ∈ u33Data.A, φ g z = z := by
    intro g hg
    rw [← hY2A] at hg
    exact hzY g hg
  let gsel : Fin 63 → U33G := fun i => Classical.choose (vHom_trans i)
  have hgsel : ∀ i, vHom (gsel i) 0 = i := fun i => Classical.choose_spec (vHom_trans i)
  let s : Fin 63 → U := fun i => φ (gsel i) z
  have s_eq : ∀ (g : U33G) (i : Fin 63), vHom g 0 = i → φ g z = s i := by
    intro g i hg
    have h2 : (vHom (gsel i))⁻¹ i = 0 := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (hgsel i).symm
    have h1 : (gsel i)⁻¹ * g ∈ stabπ vHom := by
      rw [mem_stabπ, map_mul, map_inv, Equiv.Perm.mul_apply, hg]
      exact h2
    rw [stab_vHom] at h1
    have h3 := hzA _ h1
    have h4 := congrArg (φ (gsel i)) h3
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left] at h4
    exact h4
  have hs0 : s 0 = z := by
    have h := s_eq 1 0 (by simp)
    rw [map_one] at h
    exact h.symm
  have hmk : ∀ i, (QuotientGroup.mk (s i) : U ⧸ Z) = φ' (gsel i) (QuotientGroup.mk z) := by
    intro i
    rw [hφ']
  have hεs : ∀ i, ε (QuotientGroup.mk (s i)) = i := by
    intro i
    rw [hmk, hε1, hgsel]
  have d : LiftData φ vHom Z s :=
    { sq := hsq
      zfix := hZ
      equiv := by
        intro g i
        have h := s_eq (g * gsel i) (vHom g i) (by rw [map_mul, Equiv.Perm.mul_apply, hgsel])
        rw [map_mul, MulAut.mul_apply] at h
        exact h
      inj := by
        intro i j h
        have h1 : (QuotientGroup.mk (s i * s j) : U ⧸ Z) = 1 := (QuotientGroup.eq_one_iff _).2 h
        rw [QuotientGroup.mk_mul] at h1
        have h2 : (QuotientGroup.mk (s i) : U ⧸ Z) = QuotientGroup.mk (s j) :=
          mul_right_cancel (h1.trans (hsq' (QuotientGroup.mk (s j))).symm)
        have h3 := congrArg ε h2
        rwa [hεs, hεs] at h3
      surj := by
        intro m hm
        have hm1 : (QuotientGroup.mk m : U ⧸ Z) ≠ 1 := fun h => hm ((QuotientGroup.eq_one_iff m).1 h)
        obtain ⟨g, hg⟩ := horb _ hm1
        refine ⟨vHom g 0, ?_⟩
        rw [← s_eq g (vHom g 0) rfl]
        have h2 : (QuotientGroup.mk (φ g z) : U ⧸ Z) = QuotientGroup.mk m := by
          rw [← hφ']
          exact hg
        apply (QuotientGroup.eq_one_iff _).1
        rw [QuotientGroup.mk_mul, h2]
        exact hsq' _
      nz := by
        intro i hi
        have h1 : (QuotientGroup.mk (s i) : U ⧸ Z) = 1 := (QuotientGroup.eq_one_iff _).2 hi
        rw [hmk] at h1
        exact hz' ((φ' (gsel i)).injective (by rw [h1, map_one])) }
  have hyB : u33GenPG 4 ∈ u33Data.B := u33Data.y_mem_B
  have hVB : ∀ g ∈ u33Data.B, ∀ v ∈ V, φ g v ∈ V := by
    intro g hg v hv
    exact hV g (by rw [hY1B]; exact hg) v hv
  have hs43V : s 43 ∈ V := by
    have h := s_eq (u33GenPG 4) 43 (by
      have := h_wit.1
      rwa [← vHom_gen 4] at this)
    rw [← h]
    exact hVB _ hyB z hzV
  have hs37V : s 37 ∈ V := by
    have h := s_eq (u33GenPG 4)⁻¹ 37 (by
      have h37 := h_wit.2
      rw [← vHom_gen 4] at h37
      rw [map_inv]
      exact h37)
    rw [← h]
    exact hVB _ (u33Data.B.inv_mem hyB) z hzV
  have hs0V : s 0 ∈ V := by rw [hs0]; exact hzV
  have hne1 : ∀ i, s i ≠ 1 := fun i h => d.nz i (h ▸ Z.one_mem)
  have hnei : ∀ i j, i ≠ j → s i ≠ s j := by
    intro i j hij h
    apply hij
    apply d.inj
    rw [← h]
    exact (d.sq _) ▸ Z.one_mem
  have hVeq : ((V : Subgroup U) : Set U) = ({1, s 0, s 37, s 43} : Set U) := by
    have hsub : ({1, s 0, s 37, s 43} : Set U) ⊆ (V : Set U) := by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact V.one_mem
      · exact hs0V
      · exact hs37V
      · exact hs43V
    have h4 : ({1, s 0, s 37, s 43} : Set U).ncard = 4 := by
      have e : ({1, s 0, s 37, s 43} : Set U) = ↑({1, s 0, s 37, s 43} : Finset U) := by simp
      rw [e, Set.ncard_coe_finset]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
      · exact hnei 37 43 (by decide)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hnei 0 37 (by decide), hnei 0 43 (by decide)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(hne1 0).symm, (hne1 37).symm, (hne1 43).symm⟩
    have hVn : (V : Set U).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hV4
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hVn, h4]) (Set.toFinite _)).symm
  have hVcases : ∀ v ∈ V, v = 1 ∨ v = s 0 ∨ v = s 37 ∨ v = s 43 := by
    intro v hv
    have : v ∈ ({1, s 0, s 37, s 43} : Set U) := by rw [← hVeq]; exact hv
    exact this
  have hbase0 : s 0 * s 37 = s 43 := by
    have hm : s 0 * s 37 ∈ V := V.mul_mem hs0V hs37V
    rcases hVcases _ hm with h | h | h | h
    · exact absurd (d.inj 0 37 (h ▸ Z.one_mem)) (by decide)
    · exact absurd (mul_eq_left.1 h) (hne1 37)
    · exact absurd (mul_eq_right.1 h) (hne1 0)
    · exact h
  have hD0 : s 0 * s 37 * s 43 = 1 := by
    rw [hbase0]
    exact d.sq _
  have hbase2 : s 37 * s 43 = s 0 := by
    have h1 : s 0 * (s 37 * s 43) = 1 := by rw [← mul_assoc]; exact hD0
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_eq_of_mul_eq_one_right (d.sq _)
  have hS1 : s 0 * s 1 * s 10 ∈ Z := by
    obtain ⟨h0, h1', hf⟩ := S1_cert
    refine d.forced_sum (a := 0) (b := 1) (c := 10) (by decide) [gOfWord (u33Word "Xa")] ?_ ?_
    · intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      rw [hom_gOfWord vHom vImg vHom_of]
      exact ⟨h0, h1'⟩
    · intro x hx
      apply hf
      have := hx (gOfWord (u33Word "Xa")) (by simp)
      rwa [hom_gOfWord vHom vImg vHom_of] at this
  have hS2 : s 1 * s 16 * s 15 ∈ Z := by
    obtain ⟨h0, h1', hf⟩ := S2_cert
    refine d.forced_sum (a := 1) (b := 16) (c := 15) (by decide) [gOfWord (u33Word "yxYXBa")] ?_ ?_
    · intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      rw [hom_gOfWord vHom vImg vHom_of]
      exact ⟨h0, h1'⟩
    · intro x hx
      apply hf
      have := hx (gOfWord (u33Word "yxYXBa")) (by simp)
      rwa [hom_gOfWord vHom vImg vHom_of] at this
  have hS3 : s 0 * s 15 * s 25 ∈ Z := by
    obtain ⟨h0, h1', hf⟩ := S3_cert
    refine d.forced_sum (a := 0) (b := 15) (c := 25) (by decide) [gOfWord (u33Word "XbA")] ?_ ?_
    · intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      rw [hom_gOfWord vHom vImg vHom_of]
      exact ⟨h0, h1'⟩
    · intro x hx
      apply hf
      have := hx (gOfWord (u33Word "XbA")) (by simp)
      rwa [hom_gOfWord vHom vImg vHom_of] at this
  obtain ⟨hD10, hDeq⟩ := d.key_eq (z0 := 0) (v := 1) (w := 16) (c₁ := 10) (c₂ := 15) (c₃ := 25)
    (by decide) hS1 hS2 hS3 (gOfWord (u33Word "A"))
    (by rw [hom_gOfWord vHom vImg vHom_of]; exact g1_wit.1)
    (by rw [hom_gOfWord vHom vImg vHom_of]; exact g1_wit.2.1)
    (by rw [hom_gOfWord vHom vImg vHom_of]; exact g1_wit.2.2)
  have hD1 : s 1 * s 16 * s 15 = 1 := by
    have h := d.D_inv (i := 0) (j := 37) (k := 43) (by rw [hD0]; exact Z.one_mem)
      (gOfWord (u33Word "XyxyXy"))
    rw [hom_gOfWord vHom vImg vHom_of, g2_wit.1, g2_wit.2.1, g2_wit.2.2, hD0] at h
    exact h
  have hD10' : s 10 * s 16 * s 25 = 1 := hDeq.trans hD1
  have hD8 : s 8 * s 37 * s 45 = 1 := by
    have h := d.D_inv hD10 (gOfWord (u33Word "yXYx"))
    rw [hom_gOfWord vHom vImg vHom_of, g0_wit.1, g0_wit.2.1, g0_wit.2.2, hD10'] at h
    exact h
  have hbase3 : s 8 * s 37 = s 45 := by
    have h1 : (s 8 * s 37) * s 45 = 1 := hD8
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_eq_of_mul_eq_one_right (d.sq _)
  have hbases : ∀ b ∈ baseTriples, s b.1 * s b.2.1 = s b.2.2 := by
    intro b hb
    simp only [baseTriples, List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hbase0
    · show s 37 * s 0 = s 43
      rw [mul_comm]
      exact hbase0
    · exact hbase2
    · exact hbase3
  have hclos := d.closure_of_bases baseTriples hbases {i | i ∈ cSet} (by
    intro i hi j hj hij
    obtain ⟨w, -, b, hb, h1, h2, h3⟩ := closure_wit i hi j hj hij
    refine ⟨gOfWord (u33Word w), b, hb, ?_, ?_, ?_⟩
    · rw [hom_gOfWord vHom vImg vHom_of]
      exact h1
    · rw [hom_gOfWord vHom vImg vHom_of]
      exact h2
    · rw [hom_gOfWord vHom vImg vHom_of]
      exact h3)
  let cS : Set (Fin 63) := {i | i ∈ cSet}
  let Pgrp : Subgroup U :=
    { carrier := insert 1 (s '' cS)
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | ⟨i, hi, rfl⟩
        · rw [one_mul]
          exact hb
        · rcases hb with rfl | ⟨j, hj, rfl⟩
          · rw [mul_one]
            exact Or.inr ⟨i, hi, rfl⟩
          · by_cases hij : i = j
            · subst hij
              exact Or.inl (d.sq _)
            · obtain ⟨k, hk, hk'⟩ := hclos i hi j hj hij
              exact Or.inr ⟨k, hk, hk'.symm⟩
      one_mem' := Or.inl rfl
      inv_mem' := by
        intro a ha
        rw [inv_eq_of_mul_eq_one_right (d.sq a)]
        exact ha }
  have hgen : {m : U | ∃ g ∈ Y₂, ∃ v ∈ V, m = φ g v} ⊆ (Pgrp : Set U) := by
    rintro m ⟨g, hg, v, hv, rfl⟩
    have hgA : g ∈ u33Data.A := by
      rw [← hY2A]
      exact hg
    rcases hVcases v hv with rfl | rfl | rfl | rfl
    · rw [map_one]
      exact Or.inl rfl
    · rw [d.equiv]
      exact Or.inr ⟨vHom g 0, (A_preserves g hgA 0).2 (by decide), rfl⟩
    · rw [d.equiv]
      exact Or.inr ⟨vHom g 37, (A_preserves g hgA 37).2 (by decide), rfl⟩
    · rw [d.equiv]
      exact Or.inr ⟨vHom g 43, (A_preserves g hgA 43).2 (by decide), rfl⟩
  have hle : Subgroup.closure {m : U | ∃ g ∈ Y₂, ∃ v ∈ V, m = φ g v} ≤ Pgrp :=
    (Subgroup.closure_le _).2 hgen
  refine (Subgroup.card_le_of_le hle).trans ?_
  have h7 : cS.ncard = 7 := by
    have e : cS = ↑(cSet.toFinset) := by
      ext i
      simp [cS]
    rw [e, Set.ncard_coe_finset]
    decide
  have h8 : (insert (1 : U) (s '' cS)).ncard ≤ 8 := by
    calc (insert (1 : U) (s '' cS)).ncard ≤ (s '' cS).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ cS.ncard + 1 := by
          gcongr
          exact Set.ncard_image_le (Set.toFinite _)
      _ = 8 := by rw [h7]
  have h9 : Nat.card Pgrp = (insert (1 : U) (s '' cS)).ncard := Nat.card_coe_set_eq (Pgrp : Set U)
  rw [h9]
  exact h8

end Main

end CFSG.Quasithin.ModD
