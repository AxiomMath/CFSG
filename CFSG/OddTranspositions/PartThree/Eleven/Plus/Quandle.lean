module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Perm
public import Certificates.Certificate1383002

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native


private noncomputable def plusQuandleF (k : Fin 60) : plusPerm := ⟨plusRefl k, plusRefl_mem k⟩

private theorem plusQuandleF_injective : Function.Injective plusQuandleF := by
  intro i j h
  exact plusRefl_injective (Subtype.ext_iff.mp h)

private theorem plusQuandleF_range : Set.range plusQuandleF = plusClass := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk.symm⟩

private theorem plusQuandleOfNat_val {n : ℕ} (hn : n < 60) :
    ((Fin.ofNat 60 n : Fin 60) : ℕ) = n := by
  show n % 60 = n
  rw [Nat.mod_eq_of_lt hn]

private theorem plusQuandleTf_val (i j : Fin 60) :
    ((plusQuandleTf i j : Fin 60) : ℕ) = plusQuandleT (i : ℕ) (j : ℕ) := by
  have hlt : plusQuandleT (i : ℕ) (j : ℕ) < 60 := by
    show (plusTable[(i : ℕ)]!)[(j : ℕ)]! < 60
    rw [← plusRefl_apply i j]
    exact (plusRefl i j).isLt
  show plusQuandleT (i : ℕ) (j : ℕ) % 60 = plusQuandleT (i : ℕ) (j : ℕ)
  rw [Nat.mod_eq_of_lt hlt]

private theorem plusQuandleTf_eq (i j : Fin 60) : plusQuandleTf i j = plusRefl i j := by
  apply Fin.ext
  exact (plusQuandleTf_val i j).trans (plusRefl_apply i j).symm

private theorem plusQuandleF_conj (i j : Fin 60) :
    plusQuandleF i * plusQuandleF j * (plusQuandleF i)⁻¹ = plusQuandleF (plusQuandleTf i j) := by
  apply Subtype.ext
  simp only [plusQuandleF, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  rw [plusQuandleTf_eq]
  exact plusRefl_conj i j

private theorem plusQuandleTf_conj (a i j : Fin 60) :
    plusQuandleTf a (plusQuandleTf i j) =
      plusQuandleTf (plusQuandleTf a i) (plusQuandleTf a j) := by
  apply plusRefl_injective
  simp only [plusQuandleTf_eq]
  rw [← plusRefl_conj a (plusRefl i j), ← plusRefl_conj (plusRefl a i) (plusRefl a j),
    ← plusRefl_conj a i, ← plusRefl_conj a j, ← plusRefl_conj i j]
  group

private theorem plusQuandleClosure_range_f : Subgroup.closure (Set.range plusQuandleF) = ⊤ := by
  have hset : (Subgroup.subtype plusPerm) '' Set.range plusQuandleF = Set.range plusRefl := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨plusQuandleF i, ⟨i, rfl⟩, rfl⟩
  have hmap : (Subgroup.closure (Set.range plusQuandleF)).map (Subgroup.subtype plusPerm) =
      plusPerm := by
    rw [MonoidHom.map_closure, hset, plusPerm]
  rw [eq_top_iff]
  intro x _
  have hx : (x : Equiv.Perm (Fin 60)) ∈
      (Subgroup.closure (Set.range plusQuandleF)).map (Subgroup.subtype plusPerm) := by
    rw [hmap]
    exact x.2
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  rwa [← hyx']

theorem plusClass_noncomm : ∀ a ∈ plusClass, ∃ b ∈ plusClass, ¬ Commute a b := by
  intro a ha
  obtain ⟨i, hi⟩ := ha
  have hnc : plusQuandleNoncommProp :=
    plusQuandleNoncommCheck_spec (Certificates.certificate1383002).1
  obtain ⟨j, hj⟩ := hnc i
  refine ⟨plusQuandleF j, ⟨j, rfl⟩, ?_⟩
  intro hc
  have hc' : Commute (plusRefl i) (plusRefl j) := by
    have h := congrArg (Subtype.val) hc
    show plusRefl i * plusRefl j = plusRefl j * plusRefl i
    simpa [plusQuandleF, hi] using h
  have hT : plusRefl i j = j := (commute_plusRefl_iff i j).1 hc'
  have hval : plusQuandleT (i : ℕ) (j : ℕ) = (j : ℕ) := by
    have h := congrArg Fin.val hT
    rw [plusRefl_apply] at h
    simpa [plusQuandleT] using h
  exact hj hval

private theorem plusQuandleStep_subset {S : Set (Fin 60)}
    (hblock : ∀ j : Fin 60, plusRefl j '' S = S ∨ Disjoint (plusRefl j '' S) S)
    (K : Finset (Fin 60)) (hK : (K : Set (Fin 60)) ⊆ S) :
    ((plusQuandleStepF K : Finset (Fin 60)) : Set (Fin 60)) ⊆ S := by
  intro x hx
  rw [plusQuandleStepF, Finset.coe_union, Set.mem_union] at hx
  rcases hx with hxK | hxU
  · exact hK hxK
  · rw [Finset.coe_biUnion] at hxU
    rw [Set.mem_iUnion] at hxU
    obtain ⟨j, hxU⟩ := hxU
    rw [Set.mem_iUnion] at hxU
    obtain ⟨-, hxj⟩ := hxU
    by_cases hc : ((K.image (plusQuandleTf j)) ∩ K).Nonempty
    · rw [if_pos hc] at hxj
      rw [Finset.coe_image] at hxj
      obtain ⟨k, hkK, hkx⟩ := hxj
      have hneK : (((plusQuandleTf j) '' (K : Set (Fin 60))) ∩
          (K : Set (Fin 60))).Nonempty := by
        rw [← Finset.coe_image, ← Finset.coe_inter, Finset.coe_nonempty]
        exact hc
      have hne : (((plusQuandleTf j) '' S) ∩ S).Nonempty :=
        hneK.mono (Set.inter_subset_inter (Set.image_mono hK) hK)
      have hblockTf : (plusQuandleTf j) '' S = S ∨ Disjoint ((plusQuandleTf j) '' S) S := by
        have hfun : plusQuandleTf j = plusRefl j := funext (fun k => plusQuandleTf_eq j k)
        rw [hfun]
        exact hblock j
      rcases hblockTf with heq | hdisj
      · rw [← heq]
        exact ⟨k, hK hkK, hkx⟩
      · obtain ⟨y, hy⟩ := hne
        exact (Set.disjoint_left.mp hdisj hy.1 hy.2).elim
    · rw [if_neg hc] at hxj
      exact absurd hxj (by simp)

private theorem plusQuandleIter_subset {S : Set (Fin 60)}
    (hblock : ∀ j : Fin 60, plusRefl j '' S = S ∨ Disjoint (plusRefl j '' S) S)
    (K : Finset (Fin 60)) (hK : (K : Set (Fin 60)) ⊆ S) :
    ∀ n : ℕ, ((Nat.iterate plusQuandleStepF n K : Finset (Fin 60)) : Set (Fin 60)) ⊆ S := by
  intro n
  induction n with
  | zero => simpa using hK
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact plusQuandleStep_subset hblock _ ih

theorem plusClass_primitive : ∀ B : Set plusPerm, B ⊆ plusClass → B.Nonempty →
    (∀ g : plusPerm, (fun y => g * y * g⁻¹) '' B = B ∨
      Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
    B.Subsingleton ∨ B = plusClass := by
  classical
  intro B hBsub _ hBinv
  set S : Set (Fin 60) := plusQuandleF ⁻¹' B with hSdef
  have hBeq : plusQuandleF '' S = B := by
    apply Set.image_preimage_eq_iff.mpr
    intro x hx
    rw [plusQuandleF_range]
    exact hBsub hx
  have hblock : ∀ j : Fin 60, plusRefl j '' S = S ∨ Disjoint (plusRefl j '' S) S := by
    intro j
    have h := hBinv (plusQuandleF j)
    have himg : (fun y => plusQuandleF j * y * (plusQuandleF j)⁻¹) '' B =
        plusQuandleF '' (plusRefl j '' S) := by
      rw [← hBeq]
      rw [Set.image_image, Set.image_image]
      apply Set.image_congr
      intro k _
      simpa [plusQuandleTf_eq] using plusQuandleF_conj j k
    rcases h with h | h
    · left
      rw [himg, ← hBeq] at h
      exact (Set.image_eq_image plusQuandleF_injective).1 h
    · right
      rw [himg, ← hBeq] at h
      exact (Set.disjoint_image_iff plusQuandleF_injective).1 h
  by_cases h2 : ∃ a ∈ S, ∃ b ∈ S, a ≠ b
  · right
    obtain ⟨a, ha, b, hb, hab⟩ := h2
    have hprim : plusQuandlePrimitiveProp :=
      plusQuandlePrimitiveCheck_spec (Certificates.certificate1383002).2.1
    have hiter4 : Nat.iterate plusQuandleStepF 4 ({a, b} : Finset (Fin 60)) = Finset.univ :=
      hprim a b hab
    have hsub : ((Nat.iterate plusQuandleStepF 4 ({a, b} : Finset (Fin 60)) :
        Finset (Fin 60)) : Set (Fin 60)) ⊆ S := by
      apply plusQuandleIter_subset hblock ({a, b} : Finset (Fin 60))
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    rw [hiter4, Finset.coe_univ] at hsub
    have hSuniv : S = Set.univ := Set.Subset.antisymm (Set.subset_univ _) hsub
    rw [← hBeq, hSuniv, Set.image_univ]
    exact plusQuandleF_range
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

private theorem plusQuandleAgree {a₀ : Fin 60} {θ : Fin 60 → Fin 60} {c' : ℕ}
    (hseed : plusQuandleSeed[(a₀ : ℕ)]! < 60)
    (hθhom : ∀ i j : Fin 60, θ (plusQuandleTf i j) = plusQuandleTf (θ i) (θ j))
    (hθfix : ∀ b : Fin 60, plusQuandleTf a₀ b = b → θ b = b)
    (hθc : (θ (Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!)) : ℕ) = c')
    (hseq_lt : ∀ t : Fin 60, plusQuandleSeq (a₀ : ℕ) t < 60)
    (hinj : ∀ i j : ℕ, i < 60 → j < 60 →
      plusQuandleSeq (a₀ : ℕ) i = plusQuandleSeq (a₀ : ℕ) j → i = j)
    (hcode0 : ∀ t : Fin 60, plusQuandleCode (a₀ : ℕ) t = 0 →
      plusQuandleT (a₀ : ℕ) (plusQuandleSeq (a₀ : ℕ) t) = plusQuandleSeq (a₀ : ℕ) t)
    (hcode1 : ∀ t : Fin 60, plusQuandleCode (a₀ : ℕ) t = 1 →
      plusQuandleSeq (a₀ : ℕ) t = plusQuandleSeed[(a₀ : ℕ)]!)
    (hderiv : ∀ t : Fin 60, 2 ≤ plusQuandleCode (a₀ : ℕ) t →
      (plusQuandleCode (a₀ : ℕ) t - 2) / 60 < (t : ℕ) ∧
        (plusQuandleCode (a₀ : ℕ) t - 2) % 60 < (t : ℕ) ∧
        plusQuandleT (plusQuandleSeq (a₀ : ℕ) ((plusQuandleCode (a₀ : ℕ) t - 2) / 60))
          (plusQuandleSeq (a₀ : ℕ) ((plusQuandleCode (a₀ : ℕ) t - 2) % 60)) =
          plusQuandleSeq (a₀ : ℕ) t) :
    ∀ u : Fin 60, (θ u : ℕ) = (plusQuandleMkD (a₀ : ℕ) c')[(u : ℕ)]! := by
  have hseqN : ∀ n : ℕ, n < 60 → plusQuandleSeq (a₀ : ℕ) n < 60 :=
    fun n hn => hseq_lt ⟨n, hn⟩
  let pt : ℕ → Fin 60 := fun n => Fin.ofNat 60 (plusQuandleSeq (a₀ : ℕ) n)
  have hpt : ∀ n : ℕ, n < 60 → (pt n : ℕ) = plusQuandleSeq (a₀ : ℕ) n := by
    intro n hn
    exact plusQuandleOfNat_val (hseqN n hn)
  have hpt_inj : ∀ i j : ℕ, i < 60 → j < 60 → pt i = pt j → i = j := by
    intro i j hi hj hij
    apply hinj i j hi hj
    rw [← hpt i hi, ← hpt j hj, hij]
  have hkey : ∀ t : ℕ, t < 60 →
      (θ (pt t) : ℕ) = (plusQuandleMkD (a₀ : ℕ) c')[plusQuandleSeq (a₀ : ℕ) t]! := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      have hst : plusQuandleSeq (a₀ : ℕ) t < 60 := hseqN t ht
      have hsrc : 2 ≤ plusQuandleCode (a₀ : ℕ) t →
          (plusQuandleCode (a₀ : ℕ) t - 2) / 60 < t ∧
          (plusQuandleCode (a₀ : ℕ) t - 2) % 60 < t :=
        fun hle => ⟨(hderiv ⟨t, ht⟩ hle).1, (hderiv ⟨t, ht⟩ hle).2.1⟩
      have hmkD := plusQuandleMkD_get (a₀ : ℕ) c' t ht hst hinj hsrc
      by_cases hc0 : plusQuandleCode (a₀ : ℕ) t = 0
      · rw [if_pos hc0] at hmkD
        rw [hmkD]
        have hfix : plusQuandleTf a₀ (pt t) = pt t := by
          apply Fin.ext
          rw [plusQuandleTf_val, hpt t ht, hcode0 ⟨t, ht⟩ hc0]
        rw [hθfix _ hfix, hpt t ht]
      · rw [if_neg hc0] at hmkD
        by_cases hc1 : plusQuandleCode (a₀ : ℕ) t = 1
        · rw [if_pos hc1] at hmkD
          rw [hmkD]
          have hpteq : pt t = Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!) := by
            show Fin.ofNat 60 (plusQuandleSeq (a₀ : ℕ) t) =
              Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!)
            rw [hcode1 ⟨t, ht⟩ hc1]
          rw [hpteq]
          exact hθc
        · rw [if_neg hc1] at hmkD
          rw [hmkD]
          have hle : 2 ≤ plusQuandleCode (a₀ : ℕ) t := by omega
          obtain ⟨hxl, hyl, hT⟩ := hderiv ⟨t, ht⟩ hle
          have hxlt : (plusQuandleCode (a₀ : ℕ) t - 2) / 60 < 60 := by omega
          have hylt : (plusQuandleCode (a₀ : ℕ) t - 2) % 60 < 60 := by omega
          have hpteq : pt t = plusQuandleTf (pt ((plusQuandleCode (a₀ : ℕ) t - 2) / 60))
              (pt ((plusQuandleCode (a₀ : ℕ) t - 2) % 60)) := by
            apply Fin.ext
            rw [plusQuandleTf_val, hpt _ hxlt, hpt _ hylt, hpt t ht]
            exact hT.symm
          rw [hpteq, hθhom, plusQuandleTf_val]
          rw [ih _ hxl hxlt, ih _ hyl hylt]
  intro u
  have hsurj : Function.Surjective (fun t : Fin 60 => pt (t : ℕ)) := by
    apply Finite.injective_iff_surjective.mp
    intro i j hij
    apply Fin.ext
    exact hpt_inj i j i.isLt j.isLt hij
  obtain ⟨t, htu⟩ := hsurj u
  have hseq : (pt (t : ℕ) : ℕ) = plusQuandleSeq (a₀ : ℕ) (t : ℕ) := hpt (t : ℕ) t.isLt
  rw [← htu, hseq]
  exact hkey (t : ℕ) t.isLt

theorem plusClass_perp : ∀ φ : plusPerm ≃* plusPerm, φ '' plusClass = plusClass →
    ∀ a ∈ plusClass, (∀ b ∈ plusClass, Commute a b → φ b = b) →
      (∀ x, φ x = x) ∨ ∀ x, φ x = a * x * a⁻¹ := by
  intro φ hφ a ha hfix
  obtain ⟨a₀, ha₀⟩ := ha
  have ha_eq : a = plusQuandleF a₀ := Subtype.ext ha₀
  have hφmem : ∀ k : Fin 60, φ (plusQuandleF k) ∈ plusClass := by
    intro k
    rw [← hφ]
    exact Set.mem_image_of_mem φ ⟨k, rfl⟩
  let ψ : Fin 60 → Fin 60 := fun k => Classical.choose (hφmem k)
  have hψ : ∀ k : Fin 60, φ (plusQuandleF k) = plusQuandleF (ψ k) := by
    intro k
    apply Subtype.ext
    exact Classical.choose_spec (hφmem k)
  have hψ_hom : ∀ i j : Fin 60, ψ (plusQuandleTf i j) = plusQuandleTf (ψ i) (ψ j) := by
    intro i j
    apply plusQuandleF_injective
    calc plusQuandleF (ψ (plusQuandleTf i j)) = φ (plusQuandleF (plusQuandleTf i j)) := (hψ _).symm
      _ = φ (plusQuandleF i * plusQuandleF j * (plusQuandleF i)⁻¹) := by rw [plusQuandleF_conj i j]
      _ = φ (plusQuandleF i) * φ (plusQuandleF j) * (φ (plusQuandleF i))⁻¹ := by
            simp only [map_mul, map_inv]
      _ = plusQuandleF (ψ i) * plusQuandleF (ψ j) * (plusQuandleF (ψ i))⁻¹ := by rw [hψ i, hψ j]
      _ = plusQuandleF (plusQuandleTf (ψ i) (ψ j)) := plusQuandleF_conj (ψ i) (ψ j)
  have hcomm_iff : ∀ i j : Fin 60,
      Commute (plusQuandleF i) (plusQuandleF j) ↔ Commute (plusRefl i) (plusRefl j) := by
    intro i j
    constructor
    · intro h
      exact congrArg (Subtype.val) h
    · intro h
      apply Subtype.ext
      exact h
  have hψ_fix : ∀ b : Fin 60, plusQuandleTf a₀ b = b → ψ b = b := by
    intro b hb
    have hb' : plusRefl a₀ b = b := by rw [← plusQuandleTf_eq]; exact hb
    have hcomm' : Commute (plusRefl a₀) (plusRefl b) := (commute_plusRefl_iff a₀ b).2 hb'
    have hcomm : Commute (plusQuandleF a₀) (plusQuandleF b) := (hcomm_iff a₀ b).2 hcomm'
    have hφb : φ (plusQuandleF b) = plusQuandleF b :=
      hfix (plusQuandleF b) ⟨b, rfl⟩ (by rw [ha_eq]; exact hcomm)
    rw [hψ b] at hφb
    exact plusQuandleF_injective hφb
  have hperp : plusQuandlePerpOK a₀ :=
    plusQuandlePerpCheck_spec (Certificates.certificate1383002).2.2 a₀
  obtain ⟨hseedlt, hseq_lt, hinjFin, hcode0, hcode1, hderiv, hhomBad⟩ := hperp
  have hinjNat : ∀ i j : ℕ, i < 60 → j < 60 →
      plusQuandleSeq (a₀ : ℕ) i = plusQuandleSeq (a₀ : ℕ) j → i = j := by
    intro i j hi hj hij
    have := hinjFin ⟨i, hi⟩ ⟨j, hj⟩ hij
    exact congrArg Fin.val this
  let c'' : ℕ := (ψ (Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!)) : ℕ)
  have hc''_lt : c'' < 60 := (ψ (Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!))).isLt
  have hagree : ∀ u : Fin 60, (ψ u : ℕ) = (plusQuandleMkD (a₀ : ℕ) c'')[(u : ℕ)]! :=
    plusQuandleAgree hseedlt hψ_hom hψ_fix rfl hseq_lt hinjNat hcode0 hcode1 hderiv
  have hmkD_hom : ¬ plusQuandleHomBad (plusQuandleMkD (a₀ : ℕ) c'') := by
    rintro ⟨i, j, hij⟩
    apply hij
    have hi : (plusQuandleMkD (a₀ : ℕ) c'')[(i : ℕ)]! = (ψ i : ℕ) := (hagree i).symm
    have hj : (plusQuandleMkD (a₀ : ℕ) c'')[(j : ℕ)]! = (ψ j : ℕ) := (hagree j).symm
    have hTij : (plusQuandleMkD (a₀ : ℕ) c'')[plusQuandleT (i : ℕ) (j : ℕ)]! =
        (ψ (plusQuandleTf i j) : ℕ) := by
      rw [← plusQuandleTf_val i j]
      exact (hagree (plusQuandleTf i j)).symm
    rw [hTij, hψ_hom i j, plusQuandleTf_val, ← hi, ← hj]
    rfl
  have hc''_case : c'' = plusQuandleSeed[(a₀ : ℕ)]! ∨
      c'' = plusQuandleT (a₀ : ℕ) (plusQuandleSeed[(a₀ : ℕ)]!) := by
    have h := hhomBad ⟨c'', hc''_lt⟩
    rcases h with h | h | h
    · left; exact h
    · right; exact h
    · exact absurd h hmkD_hom
  rcases hc''_case with hc | hc
  · left
    have hseedlt' : plusQuandleSeed[(a₀ : ℕ)]! < 60 := hc.symm ▸ hc''_lt
    have hθc_id : ((id (Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!)) : Fin 60) : ℕ) = c'' := by
      have h1 : ((Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!) : Fin 60) : ℕ) =
          plusQuandleSeed[(a₀ : ℕ)]! := plusQuandleOfNat_val hseedlt'
      show ((Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!) : Fin 60) : ℕ) = c''
      rw [h1, ← hc]
    have hagree_id : ∀ u : Fin 60,
        ((id u : Fin 60) : ℕ) = (plusQuandleMkD (a₀ : ℕ) c'')[(u : ℕ)]! :=
      plusQuandleAgree hseedlt (fun _ _ => rfl) (fun _ _ => rfl) hθc_id hseq_lt hinjNat
        hcode0 hcode1 hderiv
    have hψid : ∀ u : Fin 60, ψ u = u := by
      intro u
      apply Fin.ext
      have h1 := hagree u
      rw [← hagree_id u] at h1
      simpa using h1
    have hφu : ∀ u : Fin 60, φ (plusQuandleF u) = plusQuandleF u := by
      intro u
      rw [hψ u, hψid u]
    have heq : φ.toMonoidHom = MonoidHom.id plusPerm := by
      apply MonoidHom.eq_of_eqOn_dense plusQuandleClosure_range_f
      intro x hx
      obtain ⟨u, rfl⟩ := hx
      exact hφu u
    intro x
    have := DFunLike.congr_fun heq x
    simpa using this
  · right
    have hθc_conj : ((fun u : Fin 60 => plusQuandleTf a₀ u)
        (Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!)) : ℕ) = c'' := by
      have h1 : ((Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!) : Fin 60) : ℕ) =
          plusQuandleSeed[(a₀ : ℕ)]! := plusQuandleOfNat_val hseedlt
      show ((plusQuandleTf a₀ (Fin.ofNat 60 (plusQuandleSeed[(a₀ : ℕ)]!)) : Fin 60) : ℕ) = c''
      rw [plusQuandleTf_val, h1, ← hc]
    have hagree_conj : ∀ u : Fin 60,
        ((fun u : Fin 60 => plusQuandleTf a₀ u) u : ℕ) =
          (plusQuandleMkD (a₀ : ℕ) c'')[(u : ℕ)]! :=
      plusQuandleAgree hseedlt (fun _ _ => plusQuandleTf_conj a₀ _ _) (fun _ h => h) hθc_conj
        hseq_lt hinjNat hcode0 hcode1 hderiv
    have hψconj : ∀ u : Fin 60, ψ u = plusQuandleTf a₀ u := by
      intro u
      apply Fin.ext
      simpa using (hagree u).trans (hagree_conj u).symm
    have hφu : ∀ u : Fin 60,
        φ (plusQuandleF u) = plusQuandleF a₀ * plusQuandleF u * (plusQuandleF a₀)⁻¹ := by
      intro u
      rw [hψ u, hψconj u]
      exact (plusQuandleF_conj a₀ u).symm
    have heq : φ.toMonoidHom = (MulAut.conj a).toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense plusQuandleClosure_range_f
      intro x hx
      obtain ⟨u, rfl⟩ := hx
      show φ (plusQuandleF u) = a * plusQuandleF u * a⁻¹
      rw [hφu u, ha_eq]
    intro x
    have := DFunLike.congr_fun heq x
    simpa [MulAut.conj_apply] using this

end CFSG.OddTranspositions.PartThree
