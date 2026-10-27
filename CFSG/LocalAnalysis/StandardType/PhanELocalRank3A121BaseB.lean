module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A121BaseA

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private theorem plh_e_mem_W2 {c₀ y : Fin 4 → K}
    (hc₀ : c₀ ∈ (Vtail : Submodule K (Fin 4 → K)))
    (hy : y ∈ (Vtail : Submodule K (Fin 4 → K))) :
    y 3 • c₀ - c₀ 3 • y ∈ (W2 : Submodule K (Fin 4 → K)) := by
  rw [mem_W2_iff]
  constructor
  · have hc0 : c₀ 0 = 0 := by simpa [Vtail] using hc₀
    have hy0 : y 0 = 0 := by simpa [Vtail] using hy
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc0, hy0]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

private theorem plh_card_special_le_one {y : Fin 4 → K} (hy3 : y 3 ≠ 0) :
    Nat.card {s : K // 1 + y 3 * s = 0} ≤ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have h1 : y 3 * a = -1 := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using ha)
  have h2 : y 3 * b = -1 := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hb)
  exact mul_left_cancel₀ hy3 (h1.trans h2.symm)

private theorem plh_card_general_le (hK : Nat.card K = (2 ^ f) ^ 2) {c₀ δ y : Fin 4 → K}
    (hc₀ : c₀ ∈ (Vtail : Submodule K (Fin 4 → K)))
    (hy : y ∈ (Vtail : Submodule K (Fin 4 → K))) (hy3 : y 3 ≠ 0)
    (hδ : δ ∈ (W2 : Submodule K (Fin 4 → K))) (hδn : NRvec f δ) :
    Nat.card {s : K // ¬ NRvec f ((y 3 • c₀ - c₀ 3 • y) + (y 3 * s) • δ)} ≤ 2 ^ f + 1 :=
  card_not_nrvec_le f hK hδ hδn (plh_e_mem_W2 hc₀ hy) hy3

private theorem plh_arith (hq : 4 ≤ 2 ^ f) : 2 * 2 ^ f + 4 < (2 ^ f) ^ 2 := by
  have hmul : 4 * 2 ^ f ≤ (2 ^ f) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right (2 ^ f) hq
  have hlt : 2 * 2 ^ f + 4 < 4 * 2 ^ f := by
    have h4 : 4 * 2 ^ f = 2 * 2 ^ f + 2 * 2 ^ f := by ring
    omega
  omega

private theorem plh_hcard_le (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {p g : ℕ} (hp : p ≤ 1) (hg : g ≤ 2) :
    p + g * (2 ^ f + 1) + 1 < Nat.card K := by
  rw [hK]
  have hle : p + g * (2 ^ f + 1) + 1 ≤ 1 + 2 * (2 ^ f + 1) + 1 := by
    have h1 : g * (2 ^ f + 1) ≤ 2 * (2 ^ f + 1) := Nat.mul_le_mul_right _ hg
    omega
  have heq : 1 + 2 * (2 ^ f + 1) + 1 = 2 * 2 ^ f + 4 := by ring
  have hlt := plh_arith f hq
  omega

private theorem plh_exists_common (hK : Nat.card K = (2 ^ f) ^ 2)
    {c₀ δ : Fin 4 → K} (hc₀ : c₀ ∈ (Vtail : Submodule K (Fin 4 → K))) (hc3 : c₀ 3 ≠ 0)
    (hδ : δ ∈ (W2 : Submodule K (Fin 4 → K))) (hδn : NRvec f δ)
    (specs : Finset (Fin 4 → K))
    (hspecV : ∀ y ∈ specs, y ∈ (Vtail : Submodule K (Fin 4 → K)))
    (hspec3 : ∀ y ∈ specs, y 3 ≠ 0)
    (hspecδ : ∀ y ∈ specs, δ = y 3 • c₀ - c₀ 3 • y)
    (hspecCard : specs.card ≤ 1)
    (gens : Finset (Fin 4 → K))
    (hgenV : ∀ y ∈ gens, y ∈ (Vtail : Submodule K (Fin 4 → K)))
    (hgen3 : ∀ y ∈ gens, y 3 ≠ 0)
    (hcard : specs.card + gens.card * (2 ^ f + 1) + 1 < Nat.card K) :
    ∃ s : K, s ≠ 0 ∧
      (∀ y ∈ specs, NRvec f ((y 3 • c₀ - c₀ 3 • y) + (y 3 * s) • δ)) ∧
      (∀ y ∈ gens, NRvec f ((y 3 • c₀ - c₀ 3 • y) + (y 3 * s) • δ)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set badSpec : Finset K :=
    specs.biUnion (fun y => Finset.univ.filter (fun s => 1 + y 3 * s = 0)) with hbadSpec_def
  set badGen : Finset K :=
    gens.biUnion (fun y =>
      Finset.univ.filter (fun s => ¬ NRvec f ((y 3 • c₀ - c₀ 3 • y) + (y 3 * s) • δ)))
    with hbadGen_def
  set bad : Finset K := insert 0 (badSpec ∪ badGen) with hbad_def
  have hspec_le (y : Fin 4 → K) (hy3 : y 3 ≠ 0) :
      (Finset.univ.filter (fun s => 1 + y 3 * s = 0)).card ≤ 1 := by
    rw [← Fintype.card_subtype (fun s : K => 1 + y 3 * s = 0), ← Nat.card_eq_fintype_card]
    exact plh_card_special_le_one hy3
  have hgen_le (y : Fin 4 → K) (hyV : y ∈ Vtail) (hy3 : y 3 ≠ 0) :
      (Finset.univ.filter (fun s =>
        ¬ NRvec f ((y 3 • c₀ - c₀ 3 • y) + (y 3 * s) • δ))).card ≤ 2 ^ f + 1 := by
    rw [← Fintype.card_subtype
      (fun s : K => ¬ NRvec f ((y 3 • c₀ - c₀ 3 • y) + (y 3 * s) • δ)),
      ← Nat.card_eq_fintype_card]
    exact plh_card_general_le f hK hc₀ hyV hy3 hδ hδn
  have hbadSpec : badSpec.card ≤ specs.card := by
    rw [hbadSpec_def]
    calc (specs.biUnion (fun y => Finset.univ.filter (fun s => 1 + y 3 * s = 0))).card
        ≤ ∑ y ∈ specs, (Finset.univ.filter (fun s => 1 + y 3 * s = 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ y ∈ specs, 1 := Finset.sum_le_sum (fun y hy => hspec_le y (hspec3 y hy))
      _ = specs.card := by simp
  have hbadGen : badGen.card ≤ gens.card * (2 ^ f + 1) := by
    rw [hbadGen_def]
    calc (gens.biUnion (fun y => Finset.univ.filter (fun s =>
            ¬ NRvec f ((y 3 • c₀ - c₀ 3 • y) + (y 3 * s) • δ)))).card
        ≤ ∑ y ∈ gens, (Finset.univ.filter (fun s =>
            ¬ NRvec f ((y 3 • c₀ - c₀ 3 • y) + (y 3 * s) • δ))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ y ∈ gens, (2 ^ f + 1) :=
          Finset.sum_le_sum (fun y hy => hgen_le y (hgenV y hy) (hgen3 y hy))
      _ = gens.card * (2 ^ f + 1) := by simp
  have hbadCard : bad.card < Nat.card K := by
    rw [hbad_def, Nat.card_eq_fintype_card]
    calc (insert 0 (badSpec ∪ badGen)).card ≤ (badSpec ∪ badGen).card + 1 :=
          Finset.card_insert_le 0 (badSpec ∪ badGen)
      _ ≤ badSpec.card + badGen.card + 1 := by
            have := Finset.card_union_le badSpec badGen; omega
      _ ≤ specs.card + gens.card * (2 ^ f + 1) + 1 := by omega
      _ < Fintype.card K := by simpa [Nat.card_eq_fintype_card] using hcard
  obtain ⟨s, -, hsbad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := bad) (t := Finset.univ)
      (by simpa using hbadCard)
  have hs0 : s ≠ 0 := by
    intro h
    apply hsbad
    rw [h, hbad_def]
    exact Finset.mem_insert_self 0 _
  refine ⟨s, hs0, ?_, ?_⟩
  · intro y hy
    have hne : 1 + y 3 * s ≠ 0 := by
      intro h
      apply hsbad
      rw [hbad_def]
      exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inl
        (Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)))
    have heq : (y 3 • c₀ - c₀ 3 • y) + (y 3 * s) • δ = (1 + y 3 * s) • δ := by
      rw [hspecδ y hy, add_smul, one_smul]
    rw [heq]
    exact (nrvec_smul f hK hne).mpr hδn
  · intro y hy
    by_contra h
    apply hsbad
    rw [hbad_def]
    exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inr
      (Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)))

private theorem plh_BPt_line {c₀ δ : Fin 4 → K} {s : K}
    (hc₀ : c₀ ∈ (Vtail : Submodule K (Fin 4 → K))) (hc3 : c₀ 3 ≠ 0)
    (hδ : δ ∈ (W2 : Submodule K (Fin 4 → K))) :
    BPt (Submodule.span K {c₀ + s • δ}) := by
  have hδV : δ ∈ (Vtail : Submodule K (Fin 4 → K)) :=
    (Submodule.mem_inf.mp (show δ ∈ Vtail ⊓ Vsub 4 3 from hδ)).1
  have hδ3 : δ 3 = 0 := ((mem_W2_iff δ).mp hδ).2
  have hmem : c₀ + s • δ ∈ (Vtail : Submodule K (Fin 4 → K)) :=
    Vtail.add_mem hc₀ (Vtail.smul_mem s hδV)
  have hne0 : c₀ + s • δ ≠ 0 := by
    intro h0
    have h3 : (c₀ + s • δ) 3 = 0 := by simpa using congrFun h0 3
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hδ3, mul_zero, add_zero] at h3
    exact hc3 h3
  exact ⟨(Submodule.span_singleton_le_iff_mem _ _).mpr hmem, finrank_span_singleton hne0⟩

private theorem plh_BPt_of_BFl {p L : Submodule K (Fin 4 → K)} (h : BFl p L) : BPt p :=
  ⟨h.1.trans h.2.1, h.2.2.1⟩

theorem a121_nbr (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (∀ u v : Submodule K (Fin 4 → K), (∃ L, BFl u L ∧ (D121 (K := K) f).okL u L) →
      (∃ L, BFl v L ∧ (D121 (K := K) f).okL v L) →
      ∃ t, BPt t ∧ BAdj (D121 (K := K) f) u t ∧ BAdj (D121 (K := K) f) v t) ∧
    (∀ a b c d : Submodule K (Fin 4 → K), BPt a → BPt b → BPt c → BPt d →
      BAdj (D121 (K := K) f) a b → BAdj (D121 (K := K) f) b c → BAdj (D121 (K := K) f) c d →
      BAdj (D121 (K := K) f) d a →
      ∃ t, BPt t ∧ BAdj (D121 (K := K) f) a t ∧ BAdj (D121 (K := K) f) b t ∧
        BAdj (D121 (K := K) f) c t ∧ BAdj (D121 (K := K) f) d t) ∧
    (∀ u c d : Submodule K (Fin 4 → K), (∃ L, BFl u L ∧ (D121 (K := K) f).okL u L) →
      BPt c → BPt d → BAdj (D121 (K := K) f) c d →
      ∃ t, BPt t ∧ BAdj (D121 (K := K) f) u t ∧ BAdj (D121 (K := K) f) c t ∧
        BAdj (D121 (K := K) f) d t) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    obtain ⟨Lu, hBFl_u, hok_u⟩ := hu
    obtain ⟨Lv, hBFl_v, hok_v⟩ := hv
    have huPt : BPt u := plh_BPt_of_BFl hBFl_u
    have hvPt : BPt v := plh_BPt_of_BFl hBFl_v
    obtain ⟨u₀, hu_eq, hu₀V, hu₀3⟩ := exists_gen_off_V3 huPt hok_u.1
    obtain ⟨v₀, hv_eq, hv₀V, hv₀3⟩ := exists_gen_off_V3 hvPt hok_v.1
    obtain ⟨ω, hω, -, -⟩ := exists_sg_moved_avoid hK hq 0 0
    obtain ⟨hdirN, hdirW2⟩ := nrvec_dirVec f hK hω
    have hcard : (∅ : Finset (Fin 4 → K)).card +
        ({v₀} : Finset (Fin 4 → K)).card * (2 ^ f + 1) + 1 < Nat.card K :=
      plh_hcard_le f hK hq (by simp) (by simp)
    obtain ⟨s, hs0, -, hgen⟩ :=
      plh_exists_common f hK hu₀V hu₀3 hdirW2 hdirN ∅ (by simp) (by simp) (by simp) (by simp)
        {v₀} (by simp [hv₀V]) (by simp [hv₀3]) hcard
    let t : Submodule K (Fin 4 → K) := Submodule.span K {u₀ + s • dirVec ω}
    have ht : BPt t := plh_BPt_line hu₀V hu₀3 hdirW2
    have hut : BAdj (D121 (K := K) f) u t := by
      rw [hu_eq]
      exact badj121_self f hK hu₀V hu₀3 hdirW2 hdirN hs0
    have hvt : BAdj (D121 (K := K) f) v t := by
      rw [hv_eq]
      exact badj121_line f hK hu₀V hu₀3 hv₀V hv₀3 hdirW2 (hgen v₀ (by simp))
    exact ⟨t, ht, hut, hvt⟩
  · intro a b c d ha hb hc hd hab hbc hcd hda
    have hoka : (D121 (K := K) f).okL a (a ⊔ b) := hab.2.1
    have hokb : (D121 (K := K) f).okL b (a ⊔ b) := hab.2.2
    have hokc : (D121 (K := K) f).okL c (b ⊔ c) := hbc.2.2
    have hokd : (D121 (K := K) f).okL d (c ⊔ d) := hcd.2.2
    obtain ⟨a₀, ha_eq, ha₀V, ha₀3⟩ := exists_gen_off_V3 ha hoka.1
    obtain ⟨b₀, hb_eq, hb₀V, hb₀3⟩ := exists_gen_off_V3 hb hokb.1
    obtain ⟨c₀, hc_eq, hc₀V, hc₀3⟩ := exists_gen_off_V3 hc hokc.1
    obtain ⟨d₀, hd_eq, hd₀V, hd₀3⟩ := exists_gen_off_V3 hd hokd.1
    let δ : Fin 4 → K := b₀ 3 • a₀ - a₀ 3 • b₀
    have hne_ab : Submodule.span K {a₀} ≠ Submodule.span K {b₀} := by
      rw [← ha_eq, ← hb_eq]; exact hab.1
    have hab' : BAdj (D121 (K := K) f) (Submodule.span K {a₀}) (Submodule.span K {b₀}) := by
      rw [← ha_eq, ← hb_eq]; exact hab
    have hδn : NRvec f δ :=
      (badj121_iff_nrvec f hK ha₀V hb₀V ha₀3 hb₀3 hne_ab).mp hab'
    have hδW2 : δ ∈ (W2 : Submodule K (Fin 4 → K)) :=
      (sup_inf_V3 ha₀V hb₀V ha₀3 hb₀3 hne_ab).2.1
    have hcard : ({b₀} : Finset (Fin 4 → K)).card +
        (insert c₀ ({d₀} : Finset (Fin 4 → K))).card * (2 ^ f + 1) + 1 < Nat.card K :=
      plh_hcard_le f hK hq (by simp) Finset.card_le_two
    obtain ⟨s, hs0, hspec, hgen⟩ :=
      plh_exists_common f hK ha₀V ha₀3 hδW2 hδn {b₀} (by simp [hb₀V]) (by simp [hb₀3])
        (by intro y hy; rw [Finset.mem_singleton] at hy; subst hy; rfl) (by simp)
        (insert c₀ ({d₀} : Finset (Fin 4 → K)))
        (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hc₀V
          · exact hd₀V)
        (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hc₀3
          · exact hd₀3) hcard
    let t : Submodule K (Fin 4 → K) := Submodule.span K {a₀ + s • δ}
    have ht : BPt t := plh_BPt_line ha₀V ha₀3 hδW2
    have hat : BAdj (D121 (K := K) f) a t := by
      rw [ha_eq]; exact badj121_self f hK ha₀V ha₀3 hδW2 hδn hs0
    have hbt : BAdj (D121 (K := K) f) b t := by
      rw [hb_eq]; exact badj121_line f hK ha₀V ha₀3 hb₀V hb₀3 hδW2 (hspec b₀ (by simp))
    have hct : BAdj (D121 (K := K) f) c t := by
      rw [hc_eq]; exact badj121_line f hK ha₀V ha₀3 hc₀V hc₀3 hδW2 (hgen c₀ (by simp))
    have hdt : BAdj (D121 (K := K) f) d t := by
      rw [hd_eq]; exact badj121_line f hK ha₀V ha₀3 hd₀V hd₀3 hδW2 (hgen d₀ (by simp))
    exact ⟨t, ht, hat, hbt, hct, hdt⟩
  · intro u c d hu hc hd hcd
    obtain ⟨Lu, hBFl_u, hok_u⟩ := hu
    have huPt : BPt u := plh_BPt_of_BFl hBFl_u
    obtain ⟨u₀, hu_eq, hu₀V, hu₀3⟩ := exists_gen_off_V3 huPt hok_u.1
    obtain ⟨c₀, hc_eq, hc₀V, hc₀3⟩ := exists_gen_off_V3 hc hcd.2.1.1
    obtain ⟨d₀, hd_eq, hd₀V, hd₀3⟩ := exists_gen_off_V3 hd hcd.2.2.1
    let δ : Fin 4 → K := d₀ 3 • c₀ - c₀ 3 • d₀
    have hne_cd : Submodule.span K {c₀} ≠ Submodule.span K {d₀} := by
      rw [← hc_eq, ← hd_eq]; exact hcd.1
    have hcd' : BAdj (D121 (K := K) f) (Submodule.span K {c₀}) (Submodule.span K {d₀}) := by
      rw [← hc_eq, ← hd_eq]; exact hcd
    have hδn : NRvec f δ :=
      (badj121_iff_nrvec f hK hc₀V hd₀V hc₀3 hd₀3 hne_cd).mp hcd'
    have hδW2 : δ ∈ (W2 : Submodule K (Fin 4 → K)) :=
      (sup_inf_V3 hc₀V hd₀V hc₀3 hd₀3 hne_cd).2.1
    have hcard : ({d₀} : Finset (Fin 4 → K)).card +
        ({u₀} : Finset (Fin 4 → K)).card * (2 ^ f + 1) + 1 < Nat.card K :=
      plh_hcard_le f hK hq (by simp) (by simp)
    obtain ⟨s, hs0, hspec, hgen⟩ :=
      plh_exists_common f hK hc₀V hc₀3 hδW2 hδn {d₀} (by simp [hd₀V]) (by simp [hd₀3])
        (by intro y hy; rw [Finset.mem_singleton] at hy; subst hy; rfl) (by simp)
        {u₀} (by simp [hu₀V]) (by simp [hu₀3]) hcard
    let t : Submodule K (Fin 4 → K) := Submodule.span K {c₀ + s • δ}
    have ht : BPt t := plh_BPt_line hc₀V hc₀3 hδW2
    have hut : BAdj (D121 (K := K) f) u t := by
      rw [hu_eq]; exact badj121_line f hK hc₀V hc₀3 hu₀V hu₀3 hδW2 (hgen u₀ (by simp))
    have hct : BAdj (D121 (K := K) f) c t := by
      rw [hc_eq]; exact badj121_self f hK hc₀V hc₀3 hδW2 hδn hs0
    have hdt : BAdj (D121 (K := K) f) d t := by
      rw [hd_eq]; exact badj121_line f hK hc₀V hc₀3 hd₀V hd₀3 hδW2 (hspec d₀ (by simp))
    exact ⟨t, ht, hut, hct, hdt⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
