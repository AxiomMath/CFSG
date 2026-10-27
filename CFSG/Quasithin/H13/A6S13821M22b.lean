module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Hat
public import CFSG.Quasithin.Background.A3Structure321
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.A6.HatM22

open CFSG.Open CFSG.Quasithin

theorem pow_index_mem_commutator {Q : Type*} [Group Q] [Finite Q] (hQ : commutator Q = ⊤)
    (Y : Subgroup Q) {z : Q} (hz : z ∈ Subgroup.center Q) :
    ∃ hY : z ^ Y.index ∈ Y, (⟨z ^ Y.index, hY⟩ : ↥Y) ∈ commutator ↥Y := by
  classical
  let ϕ : ↥Y →* Abelianization ↥Y := Abelianization.of
  have hkey : ∀ (k : ℕ) (g₀ : Q), g₀⁻¹ * z ^ k * g₀ ∈ Y → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.mp ((Subgroup.center Q).pow_mem hz k) g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (g₀ * z ^ k) := by rw [mul_assoc, h.symm]
      _ = z ^ k := by group
  have htriv : MonoidHom.transfer ϕ z = 1 := by
    have hz' : z ∈ commutator Q := by
      rw [hQ]
      trivial
    exact Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ) hz'
  have h1 := MonoidHom.transfer_eq_pow ϕ z hkey
  rw [htriv] at h1
  refine ⟨MonoidHom.transfer_eq_pow_aux z hkey, ?_⟩
  rw [← Abelianization.ker_of]
  exact h1.symm

theorem exists_not_comm_alt6 :
    ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

theorem eq_bot_of_normal_isPGroup {P : Subgroup (alternatingGroup (Fin 6))} [P.Normal]
    (hP : IsPGroup 2 P) : P = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    rw [h, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hn
    have h3 : 3 ∣ 2 ^ n := by
      rw [← hn]
      decide
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)) (by norm_num)

theorem isHat_of_cover {W : Type} [Group W] [Finite W] (hW : commutator W = ⊤)
    (f : W →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (Z : Subgroup W) (hZc : Z ≤ Subgroup.center W) (hZ3 : Nat.card Z = 3) (hZk : Z ≤ f.ker)
    (h2 : ∀ x ∈ f.ker, x ^ 2 ∈ Z) :
    IsHat (W ⧸ CFSG.pCore 2 W) (alternatingGroup (Fin 6)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := f.ker with hN
  set O := CFSG.pCore 2 W with hO
  have hcen : ∀ z ∈ Z, ∀ w : W, z * w = w * z := fun z hz w =>
    (Subgroup.mem_center_iff.mp (hZc hz) w).symm
  have hz3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    simpa using congrArg Subtype.val this
  have hZ21 : ∀ z ∈ Z, z ^ 2 = 1 → z = 1 := fun z hz h => by
    have h3 := hz3 z hz
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h, inv_one, one_mul]
  have hNcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    have hZn : Z.Normal := ⟨fun z hz w => by rw [← hcen z hz w, mul_inv_cancel_right]; exact hz⟩
    have hc : (x * y)⁻¹ * (y * x) ∈ Z := by
      have hq : ∀ u ∈ N, (QuotientGroup.mk u : W ⧸ Z) * QuotientGroup.mk u = 1 := by
        intro u hu
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← sq]
        exact h2 u hu
      have hxq := hq x hx
      have hyq := hq y hy
      have hxyq := hq (x * y) (N.mul_mem hx hy)
      have hcomm' : (QuotientGroup.mk x : W ⧸ Z) * QuotientGroup.mk y =
          QuotientGroup.mk y * QuotientGroup.mk x := by
        rw [QuotientGroup.mk_mul] at hxyq
        have e1 : (QuotientGroup.mk x : W ⧸ Z)⁻¹ = QuotientGroup.mk x :=
          inv_eq_of_mul_eq_one_right hxq
        have e2 : (QuotientGroup.mk y : W ⧸ Z)⁻¹ = QuotientGroup.mk y :=
          inv_eq_of_mul_eq_one_right hyq
        have e3 := inv_eq_of_mul_eq_one_right hxyq
        rw [mul_inv_rev, e1, e2] at e3
        exact e3.symm
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm'
      exact hcomm'
    set c := (x * y)⁻¹ * (y * x) with hcdef
    have hyx : y * x = x * y * c := by rw [hcdef]; group
    have hx2 : x ^ 2 ∈ Z := h2 x hx
    have hc2 : c ^ 2 = 1 := by
      have e1 : y * x ^ 2 = x ^ 2 * y * c ^ 2 := by
        calc y * x ^ 2 = y * x * x := by rw [sq, mul_assoc]
          _ = x * y * c * x := by rw [hyx]
          _ = x * y * (x * c) := by rw [mul_assoc (x * y), hcen c hc x]
          _ = x * (y * x) * c := by group
          _ = x * (x * y * c) * c := by rw [hyx]
          _ = x ^ 2 * y * c ^ 2 := by rw [sq, sq]; simp only [mul_assoc]
      have e2 : y * x ^ 2 = x ^ 2 * y := (hcen _ hx2 y).symm
      rw [e2] at e1
      exact (mul_left_cancel (a := x ^ 2 * y) (by rw [mul_one]; exact e1)).symm
    have hc1 : c = 1 := hZ21 c hc hc2
    rw [hyx, hc1, mul_one]
  let P₂ : Subgroup W :=
    { carrier := {x | x ∈ N ∧ x ^ 2 = 1}
      one_mem' := ⟨N.one_mem, one_pow 2⟩
      mul_mem' := fun {a b} ha hb => ⟨N.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hNcomm a ha.1 b hb.1) 2), ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hP₂N : P₂.Normal := ⟨fun x hx w => ⟨(inferInstance : N.Normal).conj_mem x hx.1 w, by
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩⟩
  have hP₂2 : IsPGroup 2 P₂ := fun x => ⟨1, Subtype.ext (by simpa using x.2.2)⟩
  have hP₂O : P₂ ≤ O := le_sSup ⟨hP₂N, hP₂2⟩
  have hON : O ≤ N := by
    have hmapN : (O.map f).Normal := Subgroup.Normal.map inferInstance f hf
    have hmap2 : IsPGroup 2 (O.map f) := CFSG.pCore_isPGroup.map f
    have hbot : O.map f = ⊥ := eq_bot_of_normal_isPGroup hmap2
    exact (Subgroup.map_eq_bot_iff O).mp hbot
  have hOP₂ : O ≤ P₂ := by
    intro x hx
    refine ⟨hON hx, ?_⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 O) ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hx2 := h2 x (hON hx)
    have h3 := hz3 _ hx2
    have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have h4 : (x ^ 2) ^ 2 ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hk', one_pow]
    have := pow_gcd_eq_one.mpr ⟨h4, h3⟩
    rwa [hg, pow_one] at this
  have hOeq : O = P₂ := le_antisymm hOP₂ hP₂O
  let fb : W ⧸ O →* alternatingGroup (Fin 6) := QuotientGroup.lift O f (fun x hx => hON hx)
  have hfb : Function.Surjective fb := by
    intro a
    obtain ⟨x, rfl⟩ := hf a
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker : fb.ker = Z.map (QuotientGroup.mk' O) := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    constructor
    · intro hq
      have hxN : x ∈ N := hq
      refine ⟨(x ^ 2)⁻¹, Z.inv_mem (h2 x hxN), ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
      rw [hOeq]
      refine ⟨N.mul_mem (N.inv_mem (N.inv_mem (hZk (h2 x hxN)))) hxN, ?_⟩
      have e : ((x ^ 2)⁻¹)⁻¹ * x = x ^ 3 := by group
      rw [e, ← pow_mul]
      have h6 : x ^ (3 * 2) = (x ^ 2) ^ 3 := by rw [← pow_mul, mul_comm]
      rw [h6, hz3 _ (h2 x hxN)]
    · rintro ⟨z, hz, hzx⟩
      rw [← hzx]
      exact hZk hz
  have hinj : Function.Injective ((QuotientGroup.mk' O).comp Z.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hOeq] at hz
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hZ21 z z.2 hz.2)
  have hcard : Nat.card fb.ker = 3 := by
    have e : Z.map (QuotientGroup.mk' O) = ((QuotientGroup.mk' O).comp Z.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hker, e, ← hZ3]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcenter : fb.ker ≤ Subgroup.center (W ⧸ O) := by
    rw [hker]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcen z hz w]
  have hperf : commutator (W ⧸ O) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O),
      ← Subgroup.map_commutator, ← commutator_def, hW]
  exact J4M2.isHat_of_perfect_central hperf fb.ker hcenter hcard
    (QuotientGroup.quotientKerEquivOfSurjective fb hfb)
    (alternatingGroup.isSimpleGroup (by simp)) exists_not_comm_alt6

theorem comap_pCore_eq {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (g : A →* B) (hg : Function.Surjective g) (hk : IsPGroup 2 g.ker) :
    (CFSG.pCore 2 B).comap g = CFSG.pCore 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact le_sSup ⟨Subgroup.Normal.comap inferInstance g,
      CFSG.pCore_isPGroup.comap_of_ker_isPGroup g hk⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨Subgroup.Normal.map inferInstance g hg, CFSG.pCore_isPGroup.map g⟩

theorem nonempty_quotPCoreEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (g : A →* B) (hg : Function.Surjective g) (hk : IsPGroup 2 g.ker) :
    Nonempty ((A ⧸ CFSG.pCore 2 A) ≃* (B ⧸ CFSG.pCore 2 B)) := by
  let h : A →* B ⧸ CFSG.pCore 2 B := (QuotientGroup.mk' _).comp g
  have hh : Function.Surjective h := (QuotientGroup.mk'_surjective _).comp hg
  have hhk : h.ker = CFSG.pCore 2 A := by
    rw [← comap_pCore_eq g hg hk]
    ext x
    simp [h, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hhk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective h hh)⟩

theorem eq_top_of_perfect_subnormal {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    (hq : CFSG.IsQuasisimple (X ⧸ CFSG.pCore 2 X)) :
    ∀ L : Subgroup X, L ≠ ⊥ → ⁅L, L⁆ = L → IsSubnormal L ⊤ → L = ⊤ := by
  intro L
  induction L using WellFoundedLT.induction with
  | _ L ih =>
  intro hne hperf hsub
  by_cases hL : L ∈ cComp (⊤ : Subgroup X)
  · have hs : Group.IsSolvable ↥(CFSG.pCore 2 X) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥(CFSG.pCore 2 X) :=
        (CFSG.pCore_isPGroup (p := 2) (G := X)).isNilpotent
      infer_instance
    have h1 := (cComp_quotient_bijOn (CFSG.pCore 2 X) hs).mapsTo hL
    have h2 : L.map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊤ :=
      A321.cComp_eq_top_of_quasisimple hq h1
    have hLN : L ≤ Subgroup.normalizer (CFSG.pCore 2 X : Set X) := fun x _ =>
      Subgroup.mem_normalizer_iff.mpr fun n =>
        ⟨fun h => (inferInstance : (CFSG.pCore 2 X).Normal).conj_mem n h x, fun h => by
          simpa [mul_assoc] using
            (inferInstance : (CFSG.pCore 2 X).Normal).conj_mem _ h x⁻¹⟩
    have h3 := (cComp_commutator_perfectCore hL le_top hs hLN).2
    have h4 : L ⊔ CFSG.pCore 2 X = ⊤ := by
      have := QuotientGroup.comap_map_mk' (CFSG.pCore 2 X) L
      rw [h2, Subgroup.comap_top] at this
      rw [sup_comm]
      exact this.symm
    rw [h4, perfectCore_eq_self_of_perfect (by rw [← commutator_def]; exact hX)] at h3
    exact h3.symm
  · exfalso
    obtain ⟨L', hL'L, hL'ne, hL'perf, hL'sub⟩ : ∃ L' : Subgroup X, L' < L ∧ L' ≠ ⊥ ∧
        ⁅L', L'⁆ = L' ∧ IsSubnormal L' ⊤ := by
      by_contra h
      push Not at h
      exact hL ⟨hne, hperf, hsub, fun K hK hKne hKp hKs => h K hK hKne hKp hKs⟩
    have := ih L' hL'L hL'ne hL'perf hL'sub
    exact (lt_of_lt_of_le hL'L le_top).ne this

theorem mem_cComp_self {G : Type} [Group G] [Finite G] {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) : K ∈ cComp K := by
  have hKp : commutator ↥K = ⊤ := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
    exact Group.isPerfect_def.mp this
  have hne : (⊤ : Subgroup ↥K) ≠ ⊥ := by
    intro h
    obtain ⟨-, -, a, b, hab⟩ := hq
    apply hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x = 1 := by
      have : x ∈ (⊤ : Subgroup ↥K) := trivial
      rw [h, Subgroup.mem_bot] at this
      exact this
    have hy : y = 1 := by
      have : y ∈ (⊤ : Subgroup ↥K) := trivial
      rw [h, Subgroup.mem_bot] at this
      exact this
    rw [hx, hy]
  have htop : (⊤ : Subgroup ↥K) ∈ cComp (⊤ : Subgroup ↥K) := by
    refine ⟨hne, by rw [← commutator_def]; exact hKp, IsSubnormal.refl _,
      fun L hL hLne hLp hLs => ?_⟩
    exact hL.ne (eq_top_of_perfect_subnormal hKp hq L hLne hLp hLs)
  have h := map_subtype_mem_cComp htop
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

end CFSG.Quasithin.H13.A6.HatM22
