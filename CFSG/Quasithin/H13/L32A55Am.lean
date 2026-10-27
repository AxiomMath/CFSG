module

public import CFSG.Quasithin.Background.F6GoldschmidtListCat
public import CFSG.Quasithin.H13.L32AKGAutM12

public section

namespace CFSG.Quasithin.H13.L32A.T55

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {D : Type} [Group D]

theorem comm_of_sq_eq_one {U : Subgroup D} (hU2 : ∀ u ∈ U, u ^ 2 = 1) {a b : D} (ha : a ∈ U)
    (hb : b ∈ U) : a * b = b * a := by
  have hinv : ∀ u ∈ U, u⁻¹ = u := fun u hu =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hU2 u hu)
  have h1 := hinv _ (U.mul_mem ha hb)
  rw [mul_inv_rev, hinv _ hb, hinv _ ha] at h1
  exact h1.symm

theorem card_le_two_of_atMostOneInvolution {S : Type*} [Group S] [Finite S] (ι : S →* D)
    (hι : Function.Injective ι) {Z : Subgroup D} (hZ : F6.AtMostOneInvolution Z)
    (hS : ∀ s, ι s ∈ Z) (h2 : ∀ s : S, s ^ 2 = 1) : Nat.card S ≤ 2 := by
  classical
  have hne : ∀ s : S, s ≠ 1 → ι s ≠ 1 := fun s hs h => hs (hι (h.trans (map_one ι).symm))
  have hsq : ∀ s : S, ι s ^ 2 = 1 := fun s => by rw [← map_pow, h2, map_one]
  have hinj : Function.Injective (fun s : S => decide (s = 1)) := by
    intro a b hab
    by_cases ha : a = 1
    · have hb : b = 1 := by simpa [ha] using hab.symm
      rw [ha, hb]
    · have hb : b ≠ 1 := by simpa [ha] using hab.symm
      exact hι (hZ _ (hS a) _ (hS b) (hsq a) (hsq b) (hne a ha) (hne b hb))
  calc Nat.card S ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem conj_mem_centerOf {R : Subgroup D} {g z : D} (hg : g ∈ Subgroup.normalizer (R : Set D))
    (hz : z ∈ centerOf R) : g * z * g⁻¹ ∈ centerOf R := by
  obtain ⟨hzR, hzc⟩ := hz
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzR,
    Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
  have hr' : g⁻¹ * r * g ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) r).mp hr
    rwa [inv_inv] at this
  have hc : (g⁻¹ * r * g) * z = z * (g⁻¹ * r * g) := Subgroup.mem_centralizer_iff.mp hzc _ hr'
  calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * r := by group

variable [Finite D]

theorem card_le_four {R U : Subgroup D} (hUR : U ≤ R) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hZ : F6.AtMostOneInvolution (centerOf R)) (hcard : Nat.card R ≤ 2 * Nat.card U) :
    Nat.card U ≤ 4 := by
  have hc : ∀ {a b : D}, a ∈ U → b ∈ U → a * b = b * a := fun ha hb =>
    comm_of_sq_eq_one hU2 ha hb
  have hsq : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hU2 u u.2)
  by_cases hRU : R ≤ U
  · have h := card_le_two_of_atMostOneInvolution U.subtype U.subtype_injective hZ
      (fun u => ⟨hUR u.2, Subgroup.mem_centralizer_iff.mpr fun r hr => hc (hRU hr) u.2⟩) hsq
    omega
  obtain ⟨x, hxR, hxU⟩ := Set.not_subset.mp hRU
  have hidx : (U.subgroupOf R).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR] at h1
    have hne : U.relIndex R ≠ 1 := fun h => hRU (Subgroup.relIndex_eq_one.mp h)
    have hpos : 0 < Nat.card U := Nat.card_pos
    have hposR : 0 < Nat.card R := Nat.card_pos
    have hle : U.relIndex R ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have : 3 * Nat.card U ≤ U.relIndex R * Nat.card U := Nat.mul_le_mul_right _ hlt
      omega
    have h0 : U.relIndex R ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      omega
    show U.relIndex R = 2
    omega
  have hmem : ∀ {a b : D}, a ∈ R → b ∈ R → (a * b ∈ U ↔ (a ∈ U ↔ b ∈ U)) := by
    intro a b ha hb
    have := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at this
    exact this
  have hxiU : x⁻¹ ∉ U := fun h => hxU (by simpa using U.inv_mem h)
  have hx2 : x * x ∈ U := (hmem hxR hxR).mpr (iff_of_false hxU hxU)
  have hconj : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu => by
    have h1 : x * u ∉ U := fun h => hxU (((hmem hxR (hUR hu)).mp h).mpr hu)
    exact (hmem (R.mul_mem hxR (hUR hu)) (inv_mem hxR)).mpr (iff_of_false h1 hxiU)
  have hcoset : ∀ r ∈ R, r ∉ U → x⁻¹ * r ∈ U := fun r hr hrU =>
    (hmem (inv_mem hxR) hr).mpr (iff_of_false hxiU hrU)
  have hcent : ∀ u ∈ U, x * u = u * x → u ∈ centerOf R := by
    intro u hu hxu
    refine ⟨hUR hu, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    by_cases hrU : r ∈ U
    · exact hc hrU hu
    have h2 : (x⁻¹ * r) * u = u * (x⁻¹ * r) := hc (hcoset r hr hrU) hu
    calc r * u = x * ((x⁻¹ * r) * u) := by group
      _ = x * (u * (x⁻¹ * r)) := by rw [h2]
      _ = (x * u) * (x⁻¹ * r) := by group
      _ = (u * x) * (x⁻¹ * r) := by rw [hxu]
      _ = u * r := by group
  let f : ↥U →* ↥U :=
    { toFun := fun u => ⟨x * u * x⁻¹ * (u : D)⁻¹, U.mul_mem (hconj u u.2) (inv_mem u.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by
        show x * ((u : D) * v) * x⁻¹ * ((u : D) * v)⁻¹ =
          (x * u * x⁻¹ * (u : D)⁻¹) * (x * v * x⁻¹ * (v : D)⁻¹)
        have hb : (u : D)⁻¹ * (x * v * x⁻¹) = (x * v * x⁻¹) * (u : D)⁻¹ :=
          hc (inv_mem u.2) (hconj v v.2)
        have hv : (u : D)⁻¹ * (v : D)⁻¹ = (v : D)⁻¹ * (u : D)⁻¹ := hc (inv_mem u.2) (inv_mem v.2)
        calc x * ((u : D) * v) * x⁻¹ * ((u : D) * v)⁻¹
            = (x * u * x⁻¹) * ((x * v * x⁻¹) * ((v : D)⁻¹ * (u : D)⁻¹)) := by group
          _ = (x * u * x⁻¹) * ((x * v * x⁻¹) * ((u : D)⁻¹ * (v : D)⁻¹)) := by rw [hv]
          _ = (x * u * x⁻¹) * (((x * v * x⁻¹) * (u : D)⁻¹) * (v : D)⁻¹) := by group
          _ = (x * u * x⁻¹) * (((u : D)⁻¹ * (x * v * x⁻¹)) * (v : D)⁻¹) := by rw [hb]
          _ = (x * u * x⁻¹ * (u : D)⁻¹) * (x * v * x⁻¹ * (v : D)⁻¹) := by group) }
  have hf : ∀ u : ↥U, ((f u : ↥U) : D) = x * u * x⁻¹ * (u : D)⁻¹ := fun _ => rfl
  have hker : ∀ u : ↥f.ker, x * ((u : ↥U) : D) = ((u : ↥U) : D) * x := by
    intro u
    have h1 : ((f u : ↥U) : D) = 1 := by rw [MonoidHom.mem_ker.mp u.2]; rfl
    rw [hf] at h1
    have h2 : x * ((u : ↥U) : D) * x⁻¹ = (u : ↥U) := mul_inv_eq_one.mp h1
    calc x * ((u : ↥U) : D) = x * ((u : ↥U) : D) * x⁻¹ * x := by group
      _ = ((u : ↥U) : D) * x := by rw [h2]
  have hrange : ∀ w : ↥f.range, x * ((w : ↥U) : D) = ((w : ↥U) : D) * x := by
    rintro ⟨w, u, rfl⟩
    show x * ((f u : ↥U) : D) = ((f u : ↥U) : D) * x
    rw [hf]
    have hu' : (u : D)⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hU2 u u.2)
    have hxx : x * x * u = u * (x * x) := hc hx2 u.2
    have ha : (x * u * x⁻¹) * u = u * (x * u * x⁻¹) := hc (hconj u u.2) u.2
    calc x * (x * u * x⁻¹ * (u : D)⁻¹) = x * x * u * x⁻¹ * (u : D)⁻¹ := by group
      _ = u * (x * x) * x⁻¹ * (u : D)⁻¹ := by rw [hxx]
      _ = u * x * (u : D)⁻¹ := by group
      _ = u * x * u := by rw [hu']
      _ = u * (x * u * x⁻¹) * x := by group
      _ = (x * u * x⁻¹) * u * x := by rw [← ha]
      _ = x * u * x⁻¹ * (u : D)⁻¹ * x := by rw [hu']
  have hk : Nat.card f.ker ≤ 2 :=
    card_le_two_of_atMostOneInvolution (U.subtype.comp f.ker.subtype)
      (U.subtype_injective.comp f.ker.subtype_injective) hZ
      (fun u => hcent _ (u : ↥U).2 (hker u)) (fun u => Subtype.ext (hsq u))
  have hr : Nat.card f.range ≤ 2 :=
    card_le_two_of_atMostOneInvolution (U.subtype.comp f.range.subtype)
      (U.subtype_injective.comp f.range.subtype_injective) hZ
      (fun w => hcent _ (w : ↥U).2 (hrange w)) (fun w => Subtype.ext (hsq w))
  have hmul := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at hmul
  rw [← hmul]
  exact (Nat.mul_le_mul hk hr).trans (by norm_num)

omit [Finite D] in
theorem eq_one_of_mem_inf {A B : Subgroup D} (hAB : IsGoldschmidtAmalgam A B) {v : D}
    (hvT : v ∈ A ⊓ B) (hvA : v ∈ Subgroup.centralizer (A : Set D))
    (hvB : v ∈ Subgroup.centralizer (B : Set D)) : v = 1 := by
  have hle : A ⊔ B ≤ Subgroup.centralizer ({v} : Set D) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hvA a ha))
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hvB b hb))
  rw [hAB.gen] at hle
  have hg : ∀ g : D, g * v * g⁻¹ = v := fun g => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g)),
      mul_inv_cancel_right]
  have hN : (Subgroup.zpowers v).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow, hg]
    exact Subgroup.zpow_mem_zpowers v k⟩
  have h2 := hAB.toIsGoldschmidtTriple.le_pCore_of_normal_le_inf
    (N := Subgroup.zpowers v) (Subgroup.zpowers_le.mpr hvT)
  rw [hAB.pCore_eq_bot] at h2
  exact Subgroup.mem_bot.mp (h2 (Subgroup.mem_zpowers v))

omit [Finite D] in
theorem false_of_autM12 (hKG : KGAutM12E16) {W : Type} [Group W] [Finite W]
    (hW : Nonempty (W ≃* MulAut ↥quasithinM12)) {B T U : Subgroup D} {K : Subgroup W}
    (φ : ↥B ≃* ↥K) (hTB : T ≤ B) (hUT : U ≤ T) (hT : Nat.card T = 2 ^ 7)
    (hU : Nat.card U = 16) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hBU : B ≤ Subgroup.normalizer (U : Set D)) (hB : Nat.card B = 2 ^ 7 * 3) {v : D}
    (hvU : v ∈ U) (hv1 : v ≠ 1) (hvB : v ∈ Subgroup.centralizer (B : Set D)) : False := by
  set ψ : ↥B →* W := K.subtype.comp φ.toMonoidHom with hψ
  have hψi : Function.Injective ψ := K.subtype_injective.comp φ.injective
  have hcard : ∀ {S : Subgroup D}, S ≤ B → Nat.card ((S.subgroupOf B).map ψ) = Nat.card S :=
    fun hS => by
      rw [Subgroup.card_map_of_injective hψi]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  have hUB : U ≤ B := hUT.trans hTB
  have hN : ∀ b : ↥B,
      ψ b ∈ Subgroup.normalizer (((U.subgroupOf B).map ψ : Subgroup W) : Set W) := by
    intro b
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨b * u * b⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu ⊢
      simpa using (Subgroup.mem_normalizer_iff.mp (hBU b.2) u).mp hu
    · rintro ⟨u, hu, hue⟩
      refine ⟨b⁻¹ * u * b, ?_, ?_⟩
      · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu ⊢
        have := (Subgroup.mem_normalizer_iff.mp (hBU (inv_mem b.2)) u).mp hu
        simpa using this
      · rw [map_mul, map_mul, map_inv, hue]
        group
  have key := hKG W hW ((T.subgroupOf B).map ψ) ((U.subgroupOf B).map ψ) ((⊤ : Subgroup ↥B).map ψ)
    (by rw [hcard hTB, hT]) (Subgroup.map_mono (Subgroup.comap_mono hUT))
    (by rintro _ ⟨t, -, rfl⟩; exact hN t) (by rw [hcard hUB, hU])
    (by
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow]
      have : u ^ 2 = 1 := Subtype.ext (by simpa using hU2 u (Subgroup.mem_subgroupOf.mp hu))
      rw [this, map_one])
    (Subgroup.map_mono le_top) (by rintro _ ⟨b, -, rfl⟩; exact hN b)
    (by rw [Subgroup.card_map_of_injective hψi, Subgroup.card_top, hB])
  have hvB' : v ∈ B := hUB hvU
  have hmem : ψ ⟨v, hvB'⟩ ∈ (U.subgroupOf B).map ψ ⊓
      Subgroup.centralizer (((⊤ : Subgroup ↥B).map ψ : Subgroup W) : Set W) := by
    refine ⟨⟨⟨v, hvB'⟩, Subgroup.mem_subgroupOf.mpr hvU, rfl⟩, ?_⟩
    show ψ ⟨v, hvB'⟩ ∈ Subgroup.centralizer (((⊤ : Subgroup ↥B).map ψ : Subgroup W) : Set W)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, -, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hvB b b.2)
  rw [key, Subgroup.mem_bot] at hmem
  exact hv1 (congrArg Subtype.val (hψi (hmem.trans (map_one ψ).symm)))

theorem false_of_goldschmidtAmalgam (hlist : F6.GoldschmidtS3ListCat.{0}) (hKG : KGAutM12E16)
    {A B U : Subgroup D} (hAB : IsGoldschmidtAmalgam A B) (hA : CharTwo A) (hB : CharTwo B)
    (hUB : U ≤ B) (hBU : B ≤ Subgroup.normalizer (U : Set D)) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hU16 : 16 ≤ Nat.card U) {v : D} (hvU : v ∈ U) (hv1 : v ≠ 1)
    (hvB : v ∈ Subgroup.centralizer (B : Set D)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := hAB.toIsGoldschmidtTriple
  have hUp : IsPGroup 2 U := fun u => ⟨1, Subtype.ext (by simpa using hU2 u u.2)⟩
  have hUQ : U ≤ pCoreOf 2 B := le_pCoreOf_of_le_normalizer 2 hUB hBU hUp
  have hQAT : pCoreOf 2 A ≤ A ⊓ B := F6.pCoreOf_le_inf_left hT
  have hQBT : pCoreOf 2 B ≤ A ⊓ B := F6.pCoreOf_le_inf_right hT
  have hvT : v ∈ A ⊓ B := hQBT (hUQ hvU)
  have hv2 : v ^ 2 = 1 := hU2 v hvU
  have hcA := F6.card_left hT
  have hcB := F6.card_right hT
  have h6A := F6.card_left_eq_six_mul hT
  have h6B := F6.card_left_eq_six_mul hT.symm
  have hUle : Nat.card U ≤ Nat.card (pCoreOf 2 B) := Subgroup.card_le_of_le hUQ
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h48 : Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) = 48 := by
    rw [Nat.card_prod, h24]
    simp
  have hZA : ¬ F6.AtMostOneInvolution (centerOf (pCoreOf 2 A)) := by
    intro hZ
    have hvC : v ∈ Subgroup.centralizer (pCoreOf 2 A : Set D) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hQAT.trans inf_le_right)) hvB
    have hvZ : v ∈ centerOf (pCoreOf 2 A) := ⟨hA ⟨hvT.1, hvC⟩, hvC⟩
    refine hv1 (eq_one_of_mem_inf hAB hvT (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_) hvB)
    have hz := conj_mem_centerOf (le_normalizer_pCoreOf 2 A ha) hvZ
    have hne : a * v * a⁻¹ ≠ 1 := fun h => hv1 (by
      calc v = a⁻¹ * (a * v * a⁻¹) * a := by group
        _ = 1 := by rw [h]; group)
    have heq : a * v * a⁻¹ = v :=
      hZ _ hz _ hvZ (by rw [conj_pow, hv2, mul_one, mul_inv_cancel]) hv2 hne hv1
    calc a * v = a * v * a⁻¹ * a := by group
      _ = v * a := by rw [heq]
  have hsmall : F6.AtMostOneInvolution (centerOf (pCoreOf 2 B)) →
      Nat.card (pCoreOf 2 B) ≤ 2 * Nat.card U → False := fun hZ hc => by
    have := card_le_four hUQ hU2 hZ hc
    omega
  rcases F6.isGoldCaseVICat_of_charTwo (hlist D A B hAB) hA hB with h | h
  ·
    rcases h with ⟨-, -, ⟨e₁⟩, -⟩ | ⟨-, -, ⟨e₁⟩, -⟩ | ⟨-, -, -, -, hsp, -⟩ |
      ⟨-, -, -, -, hcp, -⟩ | ⟨-, -, -, -, hcp, -⟩ | ⟨-, -, -, -, -, -, hZ2, -⟩
    · have := (Nat.card_congr e₁.toEquiv).trans h24
      omega
    · have := (Nat.card_congr e₁.toEquiv).trans h48
      omega
    · exact hZA (F6.atMostOneInvolution_of_isSpecial hsp)
    · exact hZA (F6.atMostOneInvolution_of_z4_q8 hcp)
    · exact hZA (F6.atMostOneInvolution_of_q8_q8 hcp)
    · exact hZA (F6.atMostOneInvolution_of_card_eq_two hZ2)
  ·
    rcases h with ⟨-, -, ⟨e₁⟩, -⟩ | ⟨-, -, ⟨e₁⟩, -⟩ | ⟨-, -, -, -, hsp, hc2⟩ |
      ⟨-, -, -, -, hcp, ⟨e₂⟩⟩ | ⟨-, -, -, -, hcp, hc2⟩ | ⟨hY, -, -, -, -, hc1, hZ2, hc2⟩
    · have := (Nat.card_congr e₁.toEquiv).trans h24
      omega
    · have := (Nat.card_congr e₁.toEquiv).trans h48
      omega
    · exact hsmall (F6.atMostOneInvolution_of_isSpecial hsp) (by omega)
    · have h16 : Nat.card (pCoreOf 2 A) = 16 := by
        rw [Nat.card_congr e₂.toEquiv, Nat.card_prod]
        simp
      exact hsmall (F6.atMostOneInvolution_of_z4_q8 hcp) (by omega)
    · exact hsmall (F6.atMostOneInvolution_of_q8_q8 hcp) (by omega)
    ·
      have hU32 : Nat.card U < 32 := by
        by_contra hge
        push Not at hge
        exact hsmall (F6.atMostOneInvolution_of_card_eq_two hZ2) (by omega)
      have hdvd : Nat.card U ∣ 2 ^ 6 := hc1 ▸ Subgroup.card_dvd_of_le hUQ
      obtain ⟨k, hk, hUk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hU : Nat.card U = 16 := by
        rw [hUk] at hU16 hU32 ⊢
        interval_cases k <;> simp_all
      obtain ⟨W, _, _, K₁, -, hW, -, φ₁, -, -, -⟩ := hY
      exact false_of_autM12 hKG hW φ₁ (T := A ⊓ B) inf_le_right (hUQ.trans hQBT) (by omega) hU
        hU2 hBU (by omega) hvU hv1 hvB

end CFSG.Quasithin.H13.L32A.T55
