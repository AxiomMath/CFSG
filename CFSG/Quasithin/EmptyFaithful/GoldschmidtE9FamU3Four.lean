module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamIrr
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Cyc
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Cen

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.U31521

variable {G : Type} [Group G] [Finite G]

theorem involution_mem_center_u3 {L R : Subgroup G}
    (hL : IsPSU 3 2 2 ↥L) (hR : IsSylowTwoOf R L) :
    ∃ Z : Subgroup G, Nat.card Z = 4 ∧ ∀ r ∈ R, r ^ 2 = 1 → r ∈ Z := by
  obtain ⟨Z, -, -, hZcard, hZiff⟩ := exists_center_u3 (n := 2) le_rfl hL hR
  refine ⟨Z, by simpa using hZcard, fun r hr hr2 => (hZiff r).2 ⟨hr, fun y hy => ?_⟩⟩
  have hrL : r ∈ L := hR.1 hr
  have hyL : y ∈ L := hR.1 hy
  let T : Sylow 2 ↥L := A4.toSylow hR
  have hRC := rootCenterData_of_isPSU (n := 2) le_rfl hL T
  have hTmem : ∀ x : ↥L, x ∈ (T : Subgroup ↥L) ↔ (x : G) ∈ R := fun x => Iff.rfl
  have hx : (⟨r, hrL⟩ : ↥L) ∈ omegaU (T : Subgroup ↥L) := by
    refine ⟨⟨⟨r, hrL⟩, (hTmem _).2 hr⟩, Subgroup.subset_closure ?_, rfl⟩
    exact Subtype.ext (Subtype.ext (by simpa using hr2))
  have hc := ((hRC.center_iff ⟨r, hrL⟩).1 hx).2 ⟨y, hyL⟩ ((hTmem _).2 hy)
  exact congrArg Subtype.val hc

theorem noE16_U3_four {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hL : IsPSU 3 2 2 ↥L) : NoE16 S L := by
  intro V Y hVS hVN hVab hV16 hYN hYV hY5 hVY hLV
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := hVab.2
  have hYVconj : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.1 (hYV hy) v).1 hv
  have hWinv : ∀ y ∈ Y, ∀ w ∈ V ⊓ Subgroup.centralizer (L : Set G),
      y * w * y⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    intro y hy w hw
    refine ⟨hYVconj y hy w hw.1, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hl' : y⁻¹ * l * y ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hYN hy)) l).1 hl
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hw.2 _ hl'
    calc l * (y * w * y⁻¹) = y * ((y⁻¹ * l * y) * w) * y⁻¹ := by group
      _ = y * (w * (y⁻¹ * l * y)) * y⁻¹ := by rw [hc]
      _ = y * w * y⁻¹ * l := by group
  have hWbot : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rcases eq_bot_or_eq_of_five_card_sixteen hV16 hY5 hYVconj hVY inf_le_left hWinv with h | h
    · exact h
    · exfalso
      apply hLV
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_eq_left.1 h
  set S' : Subgroup G := S ⊓ Subgroup.normalizer (L : Set G) with hS'
  have hS'N : S' ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hS'2 : IsPGroup 2 ↥S' := hStd.sylow.2.1.to_le inf_le_left
  have hS'L : S' ⊓ L = S ⊓ L := by
    ext x
    simp only [hS', Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.le_normalizer h.2⟩, h.2⟩⟩
  have hSyl' : IsSylowTwoOf (S' ⊓ L) L := by
    rw [hS'L]
    exact hStd.sylowL
  obtain ⟨b, -, -, hcover⟩ := exists_involution_cover (n := 2) le_rfl hL hSyl' hS'2 hS'N
  have hVS' : V ≤ S' := le_inf hVS hVN
  set T : Subgroup G := innerPart1521 S' L with hT
  set H : Subgroup G := V ⊓ T with hH
  have h8 : 16 ≤ Nat.card H + Nat.card H := by
    by_cases hVT : V ≤ T
    · have : H = V := inf_eq_left.2 hVT
      rw [this, hV16]
      omega
    · obtain ⟨a₀, ha₀V', ha₀T⟩ := Set.not_subset.1 hVT
      have ha₀V : a₀ ∈ V := ha₀V'
      have hb0 : b⁻¹ * a₀ ∈ T := (hcover a₀ (hVS' ha₀V) (hV2 a₀ ha₀V)).resolve_left ha₀T
      have hcov : ∀ a ∈ V, a ∈ T ∨ a₀⁻¹ * a ∈ T := by
        intro a ha
        by_cases haT : a ∈ T
        · exact Or.inl haT
        · right
          have hba : b⁻¹ * a ∈ T := (hcover a (hVS' ha) (hV2 a ha)).resolve_left haT
          have := mul_mem (inv_mem hb0) hba
          simpa [mul_assoc] using this
      let f : (↥H ⊕ ↥H) → ↥V := Sum.elim (fun h => ⟨h.1, h.2.1⟩)
        (fun h => ⟨a₀ * h.1, mul_mem ha₀V h.2.1⟩)
      have hf : Function.Surjective f := by
        rintro ⟨a, ha⟩
        rcases hcov a ha with haT | haT
        · exact ⟨Sum.inl ⟨a, ha, haT⟩, rfl⟩
        · have hm : a₀⁻¹ * a ∈ V := V.mul_mem (V.inv_mem ha₀V) ha
          exact ⟨Sum.inr ⟨a₀⁻¹ * a, hm, haT⟩, Subtype.ext (by simp [f])⟩
      have := Nat.card_le_card_of_surjective f hf
      rw [Nat.card_sum, hV16] at this
      exact this
  obtain ⟨Z, hZcard, hZinv⟩ := involution_mem_center_u3 hL hStd.sylowL
  have hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    have hz1 : (⟨z, hz.1⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hz.2 g g.2)
    rw [center_eq_bot_of_isPSU le_rfl hL] at hz1
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hz1)
  have hdec : ∀ e : ↥H, ∃ r ∈ S' ⊓ L, ∃ c ∈ S' ⊓ Subgroup.centralizer (L : Set G),
      (e : G) = r * c := fun e => (mem_innerPart_iff S' L).1 e.2.2
  choose r hrR c hcC hec using hdec
  have hrZ : ∀ e : ↥H, r e ∈ Z := by
    intro e
    have hcomm := Subgroup.mem_centralizer_iff.1 (hcC e).2 (r e) (hrR e).2
    have he2 : (e : G) ^ 2 = 1 := hV2 e e.2.1
    have hr2 : (r e) ^ 2 = 1 := by
      rw [hec e, Commute.mul_pow hcomm] at he2
      have hmem : (r e) ^ 2 ∈ L ⊓ Subgroup.centralizer (L : Set G) := by
        refine ⟨pow_mem (hrR e).2 2, ?_⟩
        rw [eq_inv_of_mul_eq_one_left he2]
        exact (Subgroup.centralizer (L : Set G)).inv_mem
          ((Subgroup.centralizer (L : Set G)).pow_mem (hcC e).2 2)
      rw [hLC, Subgroup.mem_bot] at hmem
      exact hmem
    have hrR' : r e ∈ S ⊓ L := by
      rw [← hS'L]
      exact hrR e
    exact hZinv _ hrR' hr2
  let fZ : ↥H → ↥Z := fun e => ⟨r e, hrZ e⟩
  have hinj : Function.Injective fZ := by
    intro e e' hee
    have hre : r e = r e' := congrArg Subtype.val hee
    have hq : (e' : G)⁻¹ * e ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨V.mul_mem (V.inv_mem e'.2.1) e.2.1, ?_⟩
      rw [hec e, hec e', hre]
      have : (r e' * c e')⁻¹ * (r e' * c e) = (c e')⁻¹ * c e := by group
      rw [this]
      exact (Subgroup.centralizer (L : Set G)).mul_mem
        ((Subgroup.centralizer (L : Set G)).inv_mem (hcC e').2) (hcC e).2
    rw [hWbot, Subgroup.mem_bot] at hq
    exact Subtype.ext (inv_mul_eq_one.1 hq).symm
  have hle := Nat.card_le_card_of_injective fZ hinj
  omega

end CFSG.Quasithin.E9
