module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSL25
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J2Group
public import CFSG.Quasithin.Vol2.Ch10SecKHA5a

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem isSL25Group_of_block {B : Subgroup G} (hs : IsShort2 B) (hLa : IsAltType B 5)
    (hZ : blockZ B = ⊥) (hc2 : Nat.card (Subgroup.center ↥B) = 2)
    (hQ : blockQ B = blockU B ⊔ (Subgroup.center ↥B).map B.subtype) : IsSL25Group ↥B := by
  classical
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := hLa
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  have hβe' : AltCompat α β := hβe
  obtain ⟨Zc, hZcdef⟩ : ∃ Zc : Subgroup G, Zc = (Subgroup.center ↥B).map B.subtype := ⟨_, rfl⟩
  rw [← hZcdef] at hQ
  have hmem : ∀ x : ↥B, x ∈ CFSG.pCore 2 ↥B ↔ (x : G) ∈ blockQ B := fun x =>
    A5.G3.mem_pCore_iff_mem_pCoreOf x
  have hQB : blockQ B ≤ B := C1.blockQ_le B
  have hUQ : blockU B ≤ blockQ B := fun u hu => (hs.2.2.1.1 hu).1
  have hUC : blockU B ≤ Subgroup.centralizer (blockQ B : Set G) := fun u hu => (hs.2.2.1.1 hu).2
  have hUB : blockU B ≤ B := hUQ.trans hQB
  have hZQ : Zc ≤ blockQ B := by
    rw [hQ]
    exact le_sup_right
  have hZcomm : ∀ c ∈ Zc, ∀ b ∈ B, c * b = b * c := by
    rw [hZcdef]
    rintro _ ⟨z, hz, rfl⟩ b hb
    have := Subgroup.mem_center_iff.1 hz ⟨b, hb⟩
    exact (congrArg Subtype.val this).symm
  have hZC : Zc ≤ Subgroup.centralizer (blockQ B : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hZcomm c hc q (hQB hq)).symm
  have hQC : blockQ B ≤ Subgroup.centralizer (blockQ B : Set G) := by
    intro q hq
    rw [hQ] at hq
    exact sup_le hUC hZC hq
  have hcommQ : ∀ a ∈ blockQ B, ∀ b ∈ blockQ B, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hQC hb) a ha
  have hZsq : ∀ c ∈ Zc, c * c = 1 := by
    rw [hZcdef]
    rintro _ ⟨z, hz, rfl⟩
    have h1 : (⟨z, hz⟩ : ↥(Subgroup.center ↥B)) ^ Nat.card ↥(Subgroup.center ↥B) = 1 :=
      pow_card_eq_one'
    rw [hc2, pow_two] at h1
    have h2 := congrArg (fun w : ↥(Subgroup.center ↥B) => ((w : ↥B) : G)) h1
    simpa using h2
  let S : Subgroup G :=
    { carrier := {x | x ∈ blockQ B ∧ x * x = 1}
      one_mem' := ⟨(blockQ B).one_mem, mul_one 1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨(blockQ B).mul_mem ha hb, ?_⟩
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hcommQ b hb a ha]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨(blockQ B).inv_mem ha, ?_⟩
        rw [← mul_inv_rev, ha2, inv_one] }
  have hQS : blockQ B ≤ S := by
    intro q hq
    have hq' := hq
    rw [hQ] at hq'
    have hle : blockU B ⊔ Zc ≤ S :=
      sup_le (fun u hu => ⟨hUQ hu, by rw [← pow_two]; exact hs.2.2.1.2 u hu⟩)
        (fun c hc => ⟨hZQ hc, hZsq c hc⟩)
    exact hle hq'
  have hsqQ : ∀ a ∈ blockQ B, a * a = 1 := fun a ha => (hQS ha).2
  have hUcard : Nat.card (blockU B) = 16 := by
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hβinj, hβs⟩),
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5)]
    exact A5.G3.card_evenWeight_five
  have hZcard : Nat.card Zc = 2 := by
    rw [hZcdef, Subgroup.card_map_of_injective B.subtype_injective, hc2]
  have hinf : blockU B ⊓ Zc = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxZ⟩
    have hx : x ∈ blockZ B :=
      ⟨hxU, Subgroup.mem_centralizer_iff.2 fun b hb => (hZcomm x hxZ b hb).symm⟩
    rw [hZ] at hx
    exact hx
  have hZN : Zc ≤ Subgroup.normalizer (blockU B : Set G) := by
    rw [hZcdef]
    exact (Subgroup.map_subtype_le _).trans (C1.le_normalizer_blockU B)
  have hQcard : Nat.card (blockQ B) = 32 := by
    rw [hQ, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ Zc hZN
      (disjoint_iff.mpr hinf), hUcard, hZcard]
  have hpcard : Nat.card (CFSG.pCore 2 ↥B) = 32 := by
    have h1 : Nat.card ↥(blockQ B) = Nat.card ↥(CFSG.pCore 2 ↥B) := by
      unfold blockQ pCoreOf
      rw [Subgroup.card_map_of_injective B.subtype_injective]
    rw [← h1, hQcard]
  have hdecomp : ∀ q ∈ blockQ B, ∃ u ∈ blockU B, ∃ c ∈ Zc, q = u * c := by
    intro q hq
    rw [hQ] at hq
    have hq' : q ∈ ((blockU B ⊔ Zc : Subgroup G) : Set G) := hq
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ Zc hZN] at hq'
    obtain ⟨u, hu, c, hc, rfl⟩ := Set.mem_mul.mp hq'
    exact ⟨u, hu, c, hc, rfl⟩
  have hw₀ : (![0, 0, 0, 1, 1] : Fin 5 → ZMod 2) ∈ evenWeight 5 :=
    (A5.Delta5.mem_evenWeight_iff _).2 (by decide)
  obtain ⟨u₁, hu₁⟩ := hβs (Multiplicative.ofAdd (⟨![0, 0, 0, 1, 1], hw₀⟩ : evenWeight 5))
  have hu₁1 : (u₁ : G) ≠ 1 := by
    intro h1
    have h2 : u₁ = 1 := Subtype.ext h1
    rw [h2, map_one] at hu₁
    have h3 := congrArg (fun m : Multiplicative (evenWeight 5) =>
      ((Multiplicative.toAdd m : evenWeight 5) : Fin 5 → ZMod 2) 3) hu₁
    simp at h3
  refine ⟨⟨α, hαs, hαk⟩, ?_, ?_, hpcard, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hcommQ _ ((hmem a).1 ha) _ ((hmem b).1 hb))
  · intro a ha
    exact Subtype.ext (by simpa using hsqQ _ ((hmem a).1 ha))
  ·
    intro u hu
    obtain ⟨v, hv, c, hc, hq⟩ := hdecomp _ ((hmem u).1 hu)
    obtain ⟨y, hy3, hyv⟩ := exists_three_centralizing hαs hαk hβinj hβe' ⟨v, hv⟩
    refine ⟨y, hy3, Subtype.ext ?_⟩
    have h1 : (y : G) * v = v * y := mul_inv_eq_iff_eq_mul.mp hyv
    have h2 : c * y = y * c := hZcomm c hc y y.2
    show (y : G) * u = u * y
    rw [hq]
    calc (y : G) * (v * c) = (y * v) * c := by rw [mul_assoc]
      _ = (v * y) * c := by rw [h1]
      _ = v * (y * c) := by rw [mul_assoc]
      _ = v * (c * y) := by rw [← h2]
      _ = v * c * y := by rw [mul_assoc]
  ·
    obtain ⟨y, hy3, hyv⟩ := exists_three_centralizing hαs hαk hβinj hβe' u₁
    have hZne : Zc ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hZcard
      omega
    obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZne
    have hzB : z ∈ B := by
      have hz' := hz
      rw [hZcdef] at hz'
      exact Subgroup.map_subtype_le _ hz'
    refine ⟨y, hy3, ⟨u₁, hUB u₁.2⟩, (hmem _).2 (hUQ u₁.2), ⟨z, hzB⟩, (hmem _).2 (hZQ hz),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hu₁1 (congrArg Subtype.val h)
    · intro h
      have h1 : z = 1 := congrArg Subtype.val h
      exact hz1 (Subtype.ext h1)
    · intro h
      have h1 : (u₁ : G) = z := congrArg Subtype.val h
      have h2 : (u₁ : G) ∈ blockU B ⊓ Zc := ⟨u₁.2, by rw [h1]; exact hz⟩
      rw [hinf] at h2
      exact hu₁1 h2
    · exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hyv)
    · exact Subtype.ext (hZcomm z hz y y.2).symm
  ·
    have hs5 : Equiv.Perm.sign (finRotate 5) = 1 := by decide
    set σ : alternatingGroup (Fin 5) := ⟨finRotate 5, Equiv.Perm.mem_alternatingGroup.mpr hs5⟩
      with hσdef
    have hr5 : (finRotate 5) ^ 5 = 1 := by decide
    have hr1 : finRotate 5 ≠ 1 := by decide
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hσ5 : σ ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hr5)
    have hσ1 : σ ≠ 1 := fun h => hr1 (congrArg Subtype.val h)
    obtain ⟨x₀, hx₀⟩ := hαs σ
    obtain ⟨k, hk5, hkα⟩ := exists_lift_orderOf (by norm_num : Nat.Prime 5) (by norm_num) α hαk
      x₀ (by rw [hx₀]; exact hσ5) (by rw [hx₀]; exact hσ1)
    refine ⟨x₀ ^ (2 ^ k), hk5, ⟨u₁, hUB u₁.2⟩, (hmem _).2 (hUQ u₁.2), fun h => ?_⟩
    have hconj : ((x₀ ^ (2 ^ k) : ↥B) : G) * u₁ * ((x₀ ^ (2 ^ k) : ↥B) : G)⁻¹ = u₁ := by
      have h1 : ((x₀ ^ (2 ^ k) : ↥B) : G) * u₁ = u₁ * ((x₀ ^ (2 ^ k) : ↥B) : G) :=
        congrArg Subtype.val h
      rw [h1, mul_inv_cancel_right]
    have hfix := fixed_of_conj_eq hβe' _ u₁ hconj
    rw [hkα, hx₀, hu₁] at hfix
    have hpow : (σ ^ (2 ^ k)) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσ5, one_pow]
    have hτ5 : ((σ ^ (2 ^ k) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
      rw [← Subgroup.coe_pow, hpow, Subgroup.coe_one]
    have hτ1 : ((σ ^ (2 ^ k) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ≠ 1 := by
      intro h1
      have h2 : σ ^ (2 ^ k) = 1 := Subtype.ext h1
      have h3 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
      rw [orderOf_eq_prime hσ5 hσ1] at h3
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h3
      omega
    have hfix' : ∀ i, (![0, 0, 0, 1, 1] : Fin 5 → ZMod 2)
        ((((σ ^ (2 ^ k) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)))⁻¹ i) =
          (![0, 0, 0, 1, 1] : Fin 5 → ZMod 2) i := fun i => by
      simpa using hfix i
    have hw0 := A5.G3.fixed_vector_of_five _ hτ5 hτ1 _ (by decide) hfix'
    have h3 := congrFun hw0 3
    revert h3
    decide
  ·
    refine hs.1 (commutator ↥B) ?_
    intro g
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
    have hαb : α b ∈ (commutator ↥B).map α := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective α hαs,
        ← commutator_def, AppC.alt5_commutator_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨h, hh, hhb⟩ := hαb
    have hbh : b * h⁻¹ ∈ CFSG.pCore 2 ↥B := by
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hhb, mul_inv_cancel]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥B) (p := 2)) ⟨b * h⁻¹, hbh⟩
    refine ⟨k, ?_⟩
    have hk' : (b * h⁻¹) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have heq : (QuotientGroup.mk b : ↥B ⧸ commutator ↥B) = QuotientGroup.mk (b * h⁻¹) := by
      rw [QuotientGroup.eq]
      simpa using (commutator ↥B).inv_mem hh
    rw [heq, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
