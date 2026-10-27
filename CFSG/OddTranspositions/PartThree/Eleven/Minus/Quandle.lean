module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Perm
public import Certificates.Certificate1383010

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native


private noncomputable def minusQuandleF (k : Fin 65) : minusPerm := ⟨minusRefl k, minusRefl_mem k⟩

private theorem minusQuandleF_injective : Function.Injective minusQuandleF := by
  intro i j h
  exact minusRefl_injective (Subtype.ext_iff.mp h)

private theorem minusQuandleF_range : Set.range minusQuandleF = minusClass := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk.symm⟩

private theorem minusQuandleOfNat_val {n : ℕ} (hn : n < 65) :
    ((Fin.ofNat 65 n : Fin 65) : ℕ) = n := by
  show n % 65 = n
  rw [Nat.mod_eq_of_lt hn]

private theorem minusQuandleTf_val (i j : Fin 65) :
    ((minusQuandleTf i j : Fin 65) : ℕ) = minusQuandleT (i : ℕ) (j : ℕ) := by
  have hlt : minusQuandleT (i : ℕ) (j : ℕ) < 65 := by
    show (minusTable[(i : ℕ)]!)[(j : ℕ)]! < 65
    rw [← minusRefl_apply i j]
    exact (minusRefl i j).isLt
  show minusQuandleT (i : ℕ) (j : ℕ) % 65 = minusQuandleT (i : ℕ) (j : ℕ)
  rw [Nat.mod_eq_of_lt hlt]

private theorem minusQuandleTf_eq (i j : Fin 65) : minusQuandleTf i j = minusRefl i j := by
  apply Fin.ext
  exact (minusQuandleTf_val i j).trans (minusRefl_apply i j).symm

private theorem minusQuandleF_conj (i j : Fin 65) :
    minusQuandleF i * minusQuandleF j * (minusQuandleF i)⁻¹ =
      minusQuandleF (minusQuandleTf i j) := by
  apply Subtype.ext
  simp only [minusQuandleF, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  rw [minusQuandleTf_eq]
  exact minusRefl_conj i j

private theorem minusQuandleTf_conj (a i j : Fin 65) :
    minusQuandleTf a (minusQuandleTf i j) =
      minusQuandleTf (minusQuandleTf a i) (minusQuandleTf a j) := by
  apply minusRefl_injective
  simp only [minusQuandleTf_eq]
  rw [← minusRefl_conj a (minusRefl i j), ← minusRefl_conj (minusRefl a i) (minusRefl a j),
    ← minusRefl_conj a i, ← minusRefl_conj a j, ← minusRefl_conj i j]
  group

private theorem minusQuandleClosure_range_f : Subgroup.closure (Set.range minusQuandleF) = ⊤ := by
  have hset : (Subgroup.subtype minusPerm) '' Set.range minusQuandleF = Set.range minusRefl := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨minusQuandleF i, ⟨i, rfl⟩, rfl⟩
  have hmap : (Subgroup.closure (Set.range minusQuandleF)).map (Subgroup.subtype minusPerm) =
      minusPerm := by
    rw [MonoidHom.map_closure, hset, minusPerm]
  rw [eq_top_iff]
  intro x _
  have hx : (x : Equiv.Perm (Fin 65)) ∈
      (Subgroup.closure (Set.range minusQuandleF)).map (Subgroup.subtype minusPerm) := by
    rw [hmap]
    exact x.2
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  rwa [← hyx']

theorem minusClass_noncomm : ∀ a ∈ minusClass, ∃ b ∈ minusClass, ¬ Commute a b := by
  intro a ha
  obtain ⟨i, hi⟩ := ha
  have hnc : minusQuandleNoncommProp :=
    minusQuandleNoncommCheck_spec (Certificates.certificate1383010).1
  obtain ⟨j, hj⟩ := hnc i
  refine ⟨minusQuandleF j, ⟨j, rfl⟩, ?_⟩
  intro hc
  have hc' : Commute (minusRefl i) (minusRefl j) := by
    have h := congrArg (Subtype.val) hc
    show minusRefl i * minusRefl j = minusRefl j * minusRefl i
    simpa [minusQuandleF, hi] using h
  have hT : minusRefl i j = j := (commute_minusRefl_iff i j).1 hc'
  have hval : minusQuandleT (i : ℕ) (j : ℕ) = (j : ℕ) := by
    have h := congrArg Fin.val hT
    rw [minusRefl_apply] at h
    simpa [minusQuandleT] using h
  exact hj hval

private theorem minusQuandleStep_subset {S : Set (Fin 65)}
    (hblock : ∀ j : Fin 65, minusRefl j '' S = S ∨ Disjoint (minusRefl j '' S) S)
    (K : Finset (Fin 65)) (hK : (K : Set (Fin 65)) ⊆ S) :
    ((minusQuandleStepF K : Finset (Fin 65)) : Set (Fin 65)) ⊆ S := by
  intro x hx
  rw [minusQuandleStepF, Finset.coe_union, Set.mem_union] at hx
  rcases hx with hxK | hxU
  · exact hK hxK
  · rw [Finset.coe_biUnion] at hxU
    rw [Set.mem_iUnion] at hxU
    obtain ⟨j, hxU⟩ := hxU
    rw [Set.mem_iUnion] at hxU
    obtain ⟨-, hxj⟩ := hxU
    by_cases hc : ((K.image (minusQuandleTf j)) ∩ K).Nonempty
    · rw [if_pos hc] at hxj
      rw [Finset.coe_image] at hxj
      obtain ⟨k, hkK, hkx⟩ := hxj
      have hneK : (((minusQuandleTf j) '' (K : Set (Fin 65))) ∩
          (K : Set (Fin 65))).Nonempty := by
        rw [← Finset.coe_image, ← Finset.coe_inter, Finset.coe_nonempty]
        exact hc
      have hne : (((minusQuandleTf j) '' S) ∩ S).Nonempty :=
        hneK.mono (Set.inter_subset_inter (Set.image_mono hK) hK)
      have hblockTf : (minusQuandleTf j) '' S = S ∨ Disjoint ((minusQuandleTf j) '' S) S := by
        have hfun : minusQuandleTf j = minusRefl j := funext (fun k => minusQuandleTf_eq j k)
        rw [hfun]
        exact hblock j
      rcases hblockTf with heq | hdisj
      · rw [← heq]
        exact ⟨k, hK hkK, hkx⟩
      · obtain ⟨y, hy⟩ := hne
        exact (Set.disjoint_left.mp hdisj hy.1 hy.2).elim
    · rw [if_neg hc] at hxj
      exact absurd hxj (by simp)

private theorem minusQuandleIter_subset {S : Set (Fin 65)}
    (hblock : ∀ j : Fin 65, minusRefl j '' S = S ∨ Disjoint (minusRefl j '' S) S)
    (K : Finset (Fin 65)) (hK : (K : Set (Fin 65)) ⊆ S) :
    ∀ n : ℕ, ((Nat.iterate minusQuandleStepF n K : Finset (Fin 65)) : Set (Fin 65)) ⊆ S := by
  intro n
  induction n with
  | zero => simpa using hK
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact minusQuandleStep_subset hblock _ ih

theorem minusClass_primitive : ∀ B : Set minusPerm, B ⊆ minusClass → B.Nonempty →
    (∀ g : minusPerm, (fun y => g * y * g⁻¹) '' B = B ∨
      Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
    B.Subsingleton ∨ B = minusClass := by
  classical
  intro B hBsub _ hBinv
  set S : Set (Fin 65) := minusQuandleF ⁻¹' B with hSdef
  have hBeq : minusQuandleF '' S = B := by
    apply Set.image_preimage_eq_iff.mpr
    intro x hx
    rw [minusQuandleF_range]
    exact hBsub hx
  have hblock : ∀ j : Fin 65, minusRefl j '' S = S ∨ Disjoint (minusRefl j '' S) S := by
    intro j
    have h := hBinv (minusQuandleF j)
    have himg : (fun y => minusQuandleF j * y * (minusQuandleF j)⁻¹) '' B =
        minusQuandleF '' (minusRefl j '' S) := by
      rw [← hBeq]
      rw [Set.image_image, Set.image_image]
      apply Set.image_congr
      intro k _
      simpa [minusQuandleTf_eq] using minusQuandleF_conj j k
    rcases h with h | h
    · left
      rw [himg, ← hBeq] at h
      exact (Set.image_eq_image minusQuandleF_injective).1 h
    · right
      rw [himg, ← hBeq] at h
      exact (Set.disjoint_image_iff minusQuandleF_injective).1 h
  by_cases h2 : ∃ a ∈ S, ∃ b ∈ S, a ≠ b
  · right
    obtain ⟨a, ha, b, hb, hab⟩ := h2
    have hprim : minusQuandlePrimitiveProp :=
      minusQuandlePrimitiveCheck_spec (Certificates.certificate1383010).2.1
    have hiter4 : Nat.iterate minusQuandleStepF 4 ({a, b} : Finset (Fin 65)) = Finset.univ :=
      hprim a b hab
    have hsub : ((Nat.iterate minusQuandleStepF 4 ({a, b} : Finset (Fin 65)) :
        Finset (Fin 65)) : Set (Fin 65)) ⊆ S := by
      apply minusQuandleIter_subset hblock ({a, b} : Finset (Fin 65))
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    rw [hiter4, Finset.coe_univ] at hsub
    have hSuniv : S = Set.univ := Set.Subset.antisymm (Set.subset_univ _) hsub
    rw [← hBeq, hSuniv, Set.image_univ]
    exact minusQuandleF_range
  · left
    have hSsing : S.Subsingleton := by
      intro x hx y hy
      by_contra hxy
      exact h2 ⟨x, hx, y, hy, hxy⟩
    rw [← hBeq]
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨l, hl, rfl⟩ := hy
    rw [hSsing hk hl]

private theorem minusQuandleAgree {a₀ : Fin 65} {θ : Fin 65 → Fin 65} {c' : ℕ}
    (hseed : minusQuandleSeed[(a₀ : ℕ)]! < 65)
    (hθhom : ∀ i j : Fin 65, θ (minusQuandleTf i j) = minusQuandleTf (θ i) (θ j))
    (hθfix : ∀ b : Fin 65, minusQuandleTf a₀ b = b → θ b = b)
    (hθc : (θ (Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!)) : ℕ) = c')
    (hseq_lt : ∀ t : Fin 65, minusQuandleSeq (a₀ : ℕ) t < 65)
    (hinj : ∀ i j : ℕ, i < 65 → j < 65 →
      minusQuandleSeq (a₀ : ℕ) i = minusQuandleSeq (a₀ : ℕ) j → i = j)
    (hcode0 : ∀ t : Fin 65, minusQuandleCode (a₀ : ℕ) t = 0 →
      minusQuandleT (a₀ : ℕ) (minusQuandleSeq (a₀ : ℕ) t) = minusQuandleSeq (a₀ : ℕ) t)
    (hcode1 : ∀ t : Fin 65, minusQuandleCode (a₀ : ℕ) t = 1 →
      minusQuandleSeq (a₀ : ℕ) t = minusQuandleSeed[(a₀ : ℕ)]!)
    (hderiv : ∀ t : Fin 65, 2 ≤ minusQuandleCode (a₀ : ℕ) t →
      (minusQuandleCode (a₀ : ℕ) t - 2) / 65 < (t : ℕ) ∧
        (minusQuandleCode (a₀ : ℕ) t - 2) % 65 < (t : ℕ) ∧
        minusQuandleT (minusQuandleSeq (a₀ : ℕ) ((minusQuandleCode (a₀ : ℕ) t - 2) / 65))
          (minusQuandleSeq (a₀ : ℕ) ((minusQuandleCode (a₀ : ℕ) t - 2) % 65)) =
          minusQuandleSeq (a₀ : ℕ) t) :
    ∀ u : Fin 65, (θ u : ℕ) = (minusQuandleMkD (a₀ : ℕ) c')[(u : ℕ)]! := by
  have hseqN : ∀ n : ℕ, n < 65 → minusQuandleSeq (a₀ : ℕ) n < 65 :=
    fun n hn => hseq_lt ⟨n, hn⟩
  let pt : ℕ → Fin 65 := fun n => Fin.ofNat 65 (minusQuandleSeq (a₀ : ℕ) n)
  have hpt : ∀ n : ℕ, n < 65 → (pt n : ℕ) = minusQuandleSeq (a₀ : ℕ) n := by
    intro n hn
    exact minusQuandleOfNat_val (hseqN n hn)
  have hpt_inj : ∀ i j : ℕ, i < 65 → j < 65 → pt i = pt j → i = j := by
    intro i j hi hj hij
    apply hinj i j hi hj
    rw [← hpt i hi, ← hpt j hj, hij]
  have hkey : ∀ t : ℕ, t < 65 →
      (θ (pt t) : ℕ) = (minusQuandleMkD (a₀ : ℕ) c')[minusQuandleSeq (a₀ : ℕ) t]! := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      have hst : minusQuandleSeq (a₀ : ℕ) t < 65 := hseqN t ht
      have hsrc : 2 ≤ minusQuandleCode (a₀ : ℕ) t →
          (minusQuandleCode (a₀ : ℕ) t - 2) / 65 < t ∧
          (minusQuandleCode (a₀ : ℕ) t - 2) % 65 < t :=
        fun hle => ⟨(hderiv ⟨t, ht⟩ hle).1, (hderiv ⟨t, ht⟩ hle).2.1⟩
      have hmkD := minusQuandleMkD_get (a₀ : ℕ) c' t ht hst hinj hsrc
      by_cases hc0 : minusQuandleCode (a₀ : ℕ) t = 0
      · rw [if_pos hc0] at hmkD
        rw [hmkD]
        have hfix : minusQuandleTf a₀ (pt t) = pt t := by
          apply Fin.ext
          rw [minusQuandleTf_val, hpt t ht, hcode0 ⟨t, ht⟩ hc0]
        rw [hθfix _ hfix, hpt t ht]
      · rw [if_neg hc0] at hmkD
        by_cases hc1 : minusQuandleCode (a₀ : ℕ) t = 1
        · rw [if_pos hc1] at hmkD
          rw [hmkD]
          have hpteq : pt t = Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!) := by
            show Fin.ofNat 65 (minusQuandleSeq (a₀ : ℕ) t) =
              Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!)
            rw [hcode1 ⟨t, ht⟩ hc1]
          rw [hpteq]
          exact hθc
        · rw [if_neg hc1] at hmkD
          rw [hmkD]
          have hle : 2 ≤ minusQuandleCode (a₀ : ℕ) t := by omega
          obtain ⟨hxl, hyl, hT⟩ := hderiv ⟨t, ht⟩ hle
          have hxlt : (minusQuandleCode (a₀ : ℕ) t - 2) / 65 < 65 := by omega
          have hylt : (minusQuandleCode (a₀ : ℕ) t - 2) % 65 < 65 := by omega
          have hpteq : pt t = minusQuandleTf (pt ((minusQuandleCode (a₀ : ℕ) t - 2) / 65))
              (pt ((minusQuandleCode (a₀ : ℕ) t - 2) % 65)) := by
            apply Fin.ext
            rw [minusQuandleTf_val, hpt _ hxlt, hpt _ hylt, hpt t ht]
            exact hT.symm
          rw [hpteq, hθhom, minusQuandleTf_val]
          rw [ih _ hxl hxlt, ih _ hyl hylt]
  intro u
  have hsurj : Function.Surjective (fun t : Fin 65 => pt (t : ℕ)) := by
    apply Finite.injective_iff_surjective.mp
    intro i j hij
    apply Fin.ext
    exact hpt_inj i j i.isLt j.isLt hij
  obtain ⟨t, htu⟩ := hsurj u
  have hseq : (pt (t : ℕ) : ℕ) = minusQuandleSeq (a₀ : ℕ) (t : ℕ) := hpt (t : ℕ) t.isLt
  rw [← htu, hseq]
  exact hkey (t : ℕ) t.isLt

theorem minusClass_perp : ∀ φ : minusPerm ≃* minusPerm, φ '' minusClass = minusClass →
    ∀ a ∈ minusClass, (∀ b ∈ minusClass, Commute a b → φ b = b) →
      (∀ x, φ x = x) ∨ ∀ x, φ x = a * x * a⁻¹ := by
  intro φ hφ a ha hfix
  obtain ⟨a₀, ha₀⟩ := ha
  have ha_eq : a = minusQuandleF a₀ := Subtype.ext ha₀
  have hφmem : ∀ k : Fin 65, φ (minusQuandleF k) ∈ minusClass := by
    intro k
    rw [← hφ]
    exact Set.mem_image_of_mem φ ⟨k, rfl⟩
  let ψ : Fin 65 → Fin 65 := fun k => Classical.choose (hφmem k)
  have hψ : ∀ k : Fin 65, φ (minusQuandleF k) = minusQuandleF (ψ k) := by
    intro k
    apply Subtype.ext
    exact Classical.choose_spec (hφmem k)
  have hψ_hom : ∀ i j : Fin 65, ψ (minusQuandleTf i j) = minusQuandleTf (ψ i) (ψ j) := by
    intro i j
    apply minusQuandleF_injective
    calc minusQuandleF (ψ (minusQuandleTf i j)) =
          φ (minusQuandleF (minusQuandleTf i j)) := (hψ _).symm
      _ = φ (minusQuandleF i * minusQuandleF j * (minusQuandleF i)⁻¹) := by
            rw [minusQuandleF_conj i j]
      _ = φ (minusQuandleF i) * φ (minusQuandleF j) * (φ (minusQuandleF i))⁻¹ := by
            simp only [map_mul, map_inv]
      _ = minusQuandleF (ψ i) * minusQuandleF (ψ j) * (minusQuandleF (ψ i))⁻¹ := by rw [hψ i, hψ j]
      _ = minusQuandleF (minusQuandleTf (ψ i) (ψ j)) := minusQuandleF_conj (ψ i) (ψ j)
  have hcomm_iff : ∀ i j : Fin 65,
      Commute (minusQuandleF i) (minusQuandleF j) ↔ Commute (minusRefl i) (minusRefl j) := by
    intro i j
    constructor
    · intro h
      exact congrArg (Subtype.val) h
    · intro h
      apply Subtype.ext
      exact h
  have hψ_fix : ∀ b : Fin 65, minusQuandleTf a₀ b = b → ψ b = b := by
    intro b hb
    have hb' : minusRefl a₀ b = b := by rw [← minusQuandleTf_eq]; exact hb
    have hcomm' : Commute (minusRefl a₀) (minusRefl b) := (commute_minusRefl_iff a₀ b).2 hb'
    have hcomm : Commute (minusQuandleF a₀) (minusQuandleF b) := (hcomm_iff a₀ b).2 hcomm'
    have hφb : φ (minusQuandleF b) = minusQuandleF b :=
      hfix (minusQuandleF b) ⟨b, rfl⟩ (by rw [ha_eq]; exact hcomm)
    rw [hψ b] at hφb
    exact minusQuandleF_injective hφb
  have hperp : minusQuandlePerpOK a₀ :=
    minusQuandlePerpCheck_spec (Certificates.certificate1383010).2.2 a₀
  obtain ⟨hseedlt, hseq_lt, hinjFin, hcode0, hcode1, hderiv, hhomBad⟩ := hperp
  have hinjNat : ∀ i j : ℕ, i < 65 → j < 65 →
      minusQuandleSeq (a₀ : ℕ) i = minusQuandleSeq (a₀ : ℕ) j → i = j := by
    intro i j hi hj hij
    have := hinjFin ⟨i, hi⟩ ⟨j, hj⟩ hij
    exact congrArg Fin.val this
  let c'' : ℕ := (ψ (Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!)) : ℕ)
  have hc''_lt : c'' < 65 := (ψ (Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!))).isLt
  have hagree : ∀ u : Fin 65, (ψ u : ℕ) = (minusQuandleMkD (a₀ : ℕ) c'')[(u : ℕ)]! :=
    minusQuandleAgree hseedlt hψ_hom hψ_fix rfl hseq_lt hinjNat hcode0 hcode1 hderiv
  have hmkD_hom : ¬ minusQuandleHomBad (minusQuandleMkD (a₀ : ℕ) c'') := by
    rintro ⟨i, j, hij⟩
    apply hij
    have hi : (minusQuandleMkD (a₀ : ℕ) c'')[(i : ℕ)]! = (ψ i : ℕ) := (hagree i).symm
    have hj : (minusQuandleMkD (a₀ : ℕ) c'')[(j : ℕ)]! = (ψ j : ℕ) := (hagree j).symm
    have hTij : (minusQuandleMkD (a₀ : ℕ) c'')[minusQuandleT (i : ℕ) (j : ℕ)]! =
        (ψ (minusQuandleTf i j) : ℕ) := by
      rw [← minusQuandleTf_val i j]
      exact (hagree (minusQuandleTf i j)).symm
    rw [hTij, hψ_hom i j, minusQuandleTf_val, ← hi, ← hj]
    rfl
  have hc''_case : c'' = minusQuandleSeed[(a₀ : ℕ)]! ∨
      c'' = minusQuandleT (a₀ : ℕ) (minusQuandleSeed[(a₀ : ℕ)]!) := by
    have h := hhomBad ⟨c'', hc''_lt⟩
    rcases h with h | h | h
    · left; exact h
    · right; exact h
    · exact absurd h hmkD_hom
  rcases hc''_case with hc | hc
  · left
    have hseedlt' : minusQuandleSeed[(a₀ : ℕ)]! < 65 := hc.symm ▸ hc''_lt
    have hθc_id : ((id (Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!)) : Fin 65) : ℕ) = c'' := by
      have h1 : ((Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!) : Fin 65) : ℕ) =
          minusQuandleSeed[(a₀ : ℕ)]! := minusQuandleOfNat_val hseedlt'
      show ((Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!) : Fin 65) : ℕ) = c''
      rw [h1, ← hc]
    have hagree_id : ∀ u : Fin 65,
        ((id u : Fin 65) : ℕ) = (minusQuandleMkD (a₀ : ℕ) c'')[(u : ℕ)]! :=
      minusQuandleAgree hseedlt (fun _ _ => rfl) (fun _ _ => rfl) hθc_id hseq_lt hinjNat
        hcode0 hcode1 hderiv
    have hψid : ∀ u : Fin 65, ψ u = u := by
      intro u
      apply Fin.ext
      have h1 := hagree u
      rw [← hagree_id u] at h1
      simpa using h1
    have hφu : ∀ u : Fin 65, φ (minusQuandleF u) = minusQuandleF u := by
      intro u
      rw [hψ u, hψid u]
    have heq : φ.toMonoidHom = MonoidHom.id minusPerm := by
      apply MonoidHom.eq_of_eqOn_dense minusQuandleClosure_range_f
      intro x hx
      obtain ⟨u, rfl⟩ := hx
      exact hφu u
    intro x
    have := DFunLike.congr_fun heq x
    simpa using this
  · right
    have hθc_conj : ((fun u : Fin 65 => minusQuandleTf a₀ u)
        (Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!)) : ℕ) = c'' := by
      have h1 : ((Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!) : Fin 65) : ℕ) =
          minusQuandleSeed[(a₀ : ℕ)]! := minusQuandleOfNat_val hseedlt
      show ((minusQuandleTf a₀ (Fin.ofNat 65 (minusQuandleSeed[(a₀ : ℕ)]!)) : Fin 65) : ℕ) = c''
      rw [minusQuandleTf_val, h1, ← hc]
    have hagree_conj : ∀ u : Fin 65,
        ((fun u : Fin 65 => minusQuandleTf a₀ u) u : ℕ) =
          (minusQuandleMkD (a₀ : ℕ) c'')[(u : ℕ)]! :=
      minusQuandleAgree hseedlt (fun _ _ => minusQuandleTf_conj a₀ _ _) (fun _ h => h) hθc_conj
        hseq_lt hinjNat hcode0 hcode1 hderiv
    have hψconj : ∀ u : Fin 65, ψ u = minusQuandleTf a₀ u := by
      intro u
      apply Fin.ext
      simpa using (hagree u).trans (hagree_conj u).symm
    have hφu : ∀ u : Fin 65,
        φ (minusQuandleF u) = minusQuandleF a₀ * minusQuandleF u * (minusQuandleF a₀)⁻¹ := by
      intro u
      rw [hψ u, hψconj u]
      exact (minusQuandleF_conj a₀ u).symm
    have heq : φ.toMonoidHom = (MulAut.conj a).toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense minusQuandleClosure_range_f
      intro x hx
      obtain ⟨u, rfl⟩ := hx
      show φ (minusQuandleF u) = a * minusQuandleF u * a⁻¹
      rw [hφu u, ha_eq]
    intro x
    have := DFunLike.congr_fun heq x
    simpa [MulAut.conj_apply] using this

end CFSG.OddTranspositions.PartThree
