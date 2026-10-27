module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Setup
public import CFSG.Quasithin.Recognition.Stroth.Str83G5FSzTorus
import CFSG.LieType.Ree.SuzukiCoord

public section

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R CFSG.QuasithinUnique
open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.Stroth CFSG.Quasithin.Stroth.G5

private theorem pow_neg_one_val_eq_inv {n : ℕ} {ζ : GaloisField 2 n}
    (hζ : orderOf ζ = 2 ^ n - 1) (hn : 1 < 2 ^ n - 1) :
    ζ ^ ((-1 : ZMod (2 ^ n - 1)).val) = ζ⁻¹ := by
  haveI : NeZero (2 ^ n - 1) := ⟨by omega⟩
  haveI : Fact (1 < 2 ^ n - 1) := ⟨hn⟩
  have hN : ζ ^ (2 ^ n - 1) = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  rw [ZMod.neg_val, if_neg (one_ne_zero), ZMod.val_one]
  have hmul : ζ ^ (2 ^ n - 1 - 1) * ζ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ n - 1), hN]
  exact eq_inv_of_mul_eq_one_left hmul

private theorem pow_cen_val_eq {a : ℕ} (ha : 1 ≤ a) {ζ : GaloisField 2 (2 * a + 1)}
    (hζ : orderOf ζ = 2 ^ (2 * a + 1) - 1) :
    ζ ^ (-CFSG.Quasithin.Stroth.G5.cen (2 * a + 1)).val =
      (ζ⁻¹) ^ (2 ^ (a + 1) + 1) := by
  classical
  let N : ℕ := 2 ^ (2 * a + 1) - 1
  have hpow8 : 8 ≤ 2 ^ (2 * a + 1) := by
    have h3 : 3 ≤ 2 * a + 1 := by omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) h3
  have hNpos : 0 < N := by
    show 0 < 2 ^ (2 * a + 1) - 1
    omega
  have hNgt : 1 < N := by
    show 1 < 2 ^ (2 * a + 1) - 1
    omega
  haveI : NeZero N := ⟨hNpos.ne'⟩
  haveI : Fact (1 < N) := ⟨hNgt⟩
  have hζN : ζ ^ N = 1 := by
    show ζ ^ (2 ^ (2 * a + 1) - 1) = 1
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hdiv : (2 * a + 1 + 1) / 2 = a + 1 := by omega
  have hcen_eq : CFSG.Quasithin.Stroth.G5.cen (2 * a + 1) =
      ((2 ^ (a + 1) + 1 : ℕ) : ZMod N) := by
    rw [CFSG.Quasithin.Stroth.G5.cen, hdiv]
    push_cast
    ring
  have hθle : 2 ^ (a + 1) + 1 ≤ N := by
    show 2 ^ (a + 1) + 1 ≤ 2 ^ (2 * a + 1) - 1
    have hlt : 2 ^ (a + 1) + 1 < 2 ^ (2 * a + 1) := by
      have ha2 : 2 ≤ 2 ^ a := by
        have := Nat.one_lt_two_pow (n := a) (by omega)
        omega
      calc 2 ^ (a + 1) + 1 < 2 ^ (a + 1) + 2 := by omega
        _ ≤ 2 ^ (a + 1) * 2 := by omega
        _ = 2 ^ (a + 1) * 2 ^ 1 := by norm_num
        _ = 2 ^ ((a + 1) + 1) := by rw [← pow_add]
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcast1 : ((((-CFSG.Quasithin.Stroth.G5.cen (2 * a + 1)).val : ℕ) : ZMod N)) =
      -CFSG.Quasithin.Stroth.G5.cen (2 * a + 1) := ZMod.natCast_zmod_val _
  have hcast2 : (((N - (2 ^ (a + 1) + 1) : ℕ) : ZMod N)) =
      -((2 ^ (a + 1) + 1 : ℕ) : ZMod N) := by
    rw [Nat.cast_sub hθle, ZMod.natCast_self, zero_sub]
  have hcast : ((((-CFSG.Quasithin.Stroth.G5.cen (2 * a + 1)).val : ℕ) : ZMod N)) =
      ((N - (2 ^ (a + 1) + 1) : ℕ) : ZMod N) := by
    rw [hcast1, hcen_eq, hcast2]
  have hζNsub : ζ ^ (N - (2 ^ (a + 1) + 1)) = (ζ⁻¹) ^ (2 ^ (a + 1) + 1) := by
    have hmul : ζ ^ (N - (2 ^ (a + 1) + 1)) * ζ ^ (2 ^ (a + 1) + 1) = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hθle, hζN]
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [pow_eq_pow_of_natCast_eq hζ hcast, hζNsub]

theorem CFSG.Quasithin.Stroth.G5.exists_szEmb {G : Type}
    [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : Hyp111 L1 L2 S) (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hB : bigB L1 L2 S ≤ normalizer (S : Set G))
    {D : Subgroup G} (hD : RonanF13.HallTwoPrime D (borelOf L1 S))
    (hBD : borelOf L1 S = (S ⊓ L1) ⊔ D)
    {ζ : GaloisField 2 (2 * a + 1)} (hζ : orderOf ζ = 2 ^ (2 * a + 1) - 1) :
    ∃ (d₁ : G) (X₀ : Subgroup G) (β β' : G → GaloisField 2 (2 * a + 1)),
      zpowers d₁ = D ∧ orderOf d₁ = 2 ^ (2 * a + 1) - 1 ∧
      pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ X₀ ∧ X₀ ≤ S ∧
      bigB L1 L2 S ≤ normalizer (X₀ : Set G) ∧
      (∀ s ∈ S, s ∉ X₀ → s ^ 2 ∈ X₀ ∧ s ^ 2 ∉ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      CFSG.Quasithin.Stroth.G5.IsChiEmb₁ ζ d₁ X₀ S (-1) β ∧
      CFSG.Quasithin.Stroth.G5.IsChiEmb₁ ζ d₁ (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) X₀
        (-CFSG.Quasithin.Stroth.G5.cen (2 * a + 1)) β' := by
  classical
  let K := GaloisField 2 (2 * a + 1)
  let N : ℕ := 2 ^ (2 * a + 1) - 1
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by
    have := GaloisField.card 2 (2 * a + 1) (by omega)
    simpa [K] using this
  have hpow8 : 8 ≤ 2 ^ (2 * a + 1) := by
    have h3 : 3 ≤ 2 * a + 1 := by omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) h3
  have hNpos : 0 < N := by
    show 0 < 2 ^ (2 * a + 1) - 1
    omega
  have hNgt : 1 < N := by
    show 1 < 2 ^ (2 * a + 1) - 1
    omega
  haveI : NeZero N := ⟨hNpos.ne'⟩
  haveI : Fact (1 < N) := ⟨hNgt⟩
  have hζN : ζ ^ N = 1 := by
    show ζ ^ (2 ^ (2 * a + 1) - 1) = 1
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hNpos.ne'] at hζN
    exact zero_ne_one hζN
  let l : Kˣ := Units.mk0 ζ hζ0
  have hl : orderOf l = 2 ^ (2 * a + 1) - 1 := by
    rw [← orderOf_units (y := l)]
    show orderOf (l : K) = 2 ^ (2 * a + 1) - 1
    simpa [l] using hζ
  obtain ⟨e, d, hSmap, hzpow, horder, hdE⟩ :=
    CFSG.Quasithin.Stroth.G5F.exists_vertexEquiv_torus (K := K) hK hF hB ha hSz hD hBD hl
  obtain ⟨hpCore, hQ1S, -, -⟩ :=
    CFSG.Quasithin.Stroth.G5F.sz_vertex (K := K) hK hF hB ha hSz
  let d₁ : G := (d : G)
  let ψ : ↥(L1 ⊔ S) →* suzukiGroup a K :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)))
  let X₀ : Subgroup G := ((suzukiZ0 a K).comap ψ).map (L1 ⊔ S).subtype
  have hψd : ψ d = suzukiDElt a K l := by
    simpa [ψ] using hdE
  have hψ_mem_U : ∀ s : ↥(L1 ⊔ S), (s : G) ∈ S → ψ s ∈ suzukiU a K := by
    intro s hs
    have hsbar : QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) s ∈ szSbar L1 L2 S :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
    have h := Subgroup.mem_map_of_mem e.toMonoidHom hsbar
    rw [hSmap] at h
    simpa [ψ] using h
  have hmemX0 : ∀ t : G, t ∈ X₀ ↔ t ∈ S ∧ t ^ 2 ∈ Q1 L1 L2 S := by
    intro t
    constructor
    · intro ht
      obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp ht
      have hxZ : ψ x ∈ suzukiZ0 a K := (Subgroup.mem_comap).mp hx
      have hxU : ψ x ∈ suzukiU a K := suzukiZ0_le_suzukiU hxZ
      have hmk : QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) x ∈ szSbar L1 L2 S := by
        have h1 : e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) x) ∈
            (szSbar L1 L2 S).map e.toMonoidHom := by
          rw [hSmap]
          exact hxU
        obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp h1
        have hyx : y = QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) x := by
          apply e.injective
          exact hye
        rwa [hyx] at hy
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmk
      have hyS : (y : G) ∈ S := Subgroup.mem_subgroupOf.mp hy
      have hx_y : (x * y⁻¹ : ↥(L1 ⊔ S)) ∈ pCore 2 ↥(L1 ⊔ S) := by
        refine (QuotientGroup.eq_one_iff (x * y⁻¹)).mp ?_
        have hyx' : (↑y : oTwoQuot ↥(L1 ⊔ S)) = ↑x := by
          simpa only [QuotientGroup.mk'_apply] using hyx
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hyx', mul_inv_cancel]
      have hxQ1 : ((x * y⁻¹ : ↥(L1 ⊔ S)) : G) ∈ Q1 L1 L2 S := by
        have h := (CFSG.Quasithin.F1.mem_pCore_iff_coe (x * y⁻¹)).mp hx_y
        rwa [hpCore] at h
      have hxS : (x : G) ∈ S := by
        have h1 : ((x * y⁻¹ : ↥(L1 ⊔ S)) : G) ∈ S := hQ1S hxQ1
        have h2 : ((x * y⁻¹ : ↥(L1 ⊔ S)) : G) * (y : G) = (x : G) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [← h2]
        exact S.mul_mem h1 hyS
      have hsqZ : (ψ x) ^ 2 = 1 :=
        ((CFSG.ShultStronglyClosedTI.SuzukiLayerKernel.mem_suzukiZ0_iff_sq_eq_one hK).mp hxZ).2
      have hx2ker : x ^ 2 ∈ pCore 2 ↥(L1 ⊔ S) := by
        refine (QuotientGroup.eq_one_iff (x ^ 2)).mp ?_
        have h2 : e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) (x ^ 2)) = 1 := by
          rw [show e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) (x ^ 2)) = ψ (x ^ 2) from rfl,
            map_pow, hsqZ]
        exact e.injective (by rw [map_one]; exact h2)
      have hx2Q1 : (x : G) ^ 2 ∈ Q1 L1 L2 S := by
        have h := (CFSG.Quasithin.F1.mem_pCore_iff_coe (x ^ 2)).mp hx2ker
        rw [hpCore] at h
        simpa using h
      exact ⟨by rw [← hxt]; exact hxS, by rw [← hxt]; exact hx2Q1⟩
    · rintro ⟨htS, ht2⟩
      have htLS : t ∈ L1 ⊔ S := Subgroup.mem_sup_right htS
      have hxU : ψ ⟨t, htLS⟩ ∈ suzukiU a K := hψ_mem_U _ htS
      have ht2S : t ^ 2 ∈ S := by
        simpa [pow_two] using S.mul_mem htS htS
      have ht2LS : t ^ 2 ∈ L1 ⊔ S := Subgroup.mem_sup_right ht2S
      have hmem : (⟨t ^ 2, ht2LS⟩ : ↥(L1 ⊔ S)) ∈ pCore 2 ↥(L1 ⊔ S) := by
        refine (CFSG.Quasithin.F1.mem_pCore_iff_coe _).mpr ?_
        rw [hpCore]
        simpa using ht2
      have hsq1 : ψ (⟨t, htLS⟩ ^ 2) = 1 := by
        have h2 : (⟨t, htLS⟩ : ↥(L1 ⊔ S)) ^ 2 = ⟨t ^ 2, ht2LS⟩ := Subtype.ext rfl
        rw [h2]
        have hker : QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) ⟨t ^ 2, ht2LS⟩ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hmem
        rw [show ψ ⟨t ^ 2, ht2LS⟩ =
          e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) ⟨t ^ 2, ht2LS⟩) from rfl, hker, map_one]
      have hxZ : ψ ⟨t, htLS⟩ ∈ suzukiZ0 a K :=
        (CFSG.ShultStronglyClosedTI.SuzukiLayerKernel.mem_suzukiZ0_iff_sq_eq_one hK).mpr
          ⟨hxU, by rw [← map_pow]; exact hsq1⟩
      exact Subgroup.mem_map_of_mem (L1 ⊔ S).subtype
        (show ⟨t, htLS⟩ ∈ (suzukiZ0 a K).comap ψ from hxZ)
  have hX0_le_S : X₀ ≤ S := fun t ht => ((hmemX0 t).mp ht).1
  have hQ1_le_X0 : Q1 L1 L2 S ≤ X₀ := by
    intro q hq
    exact (hmemX0 q).mpr ⟨hQ1S hq, by simpa [pow_two] using (Q1 L1 L2 S).mul_mem hq hq⟩
  have hX0_Z : ∀ s : G, s ∈ X₀ → ∀ h : s ∈ L1 ⊔ S, ψ ⟨s, h⟩ ∈ suzukiZ0 a K := by
    intro s hs h
    obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp hs
    have hyZ : ψ y ∈ suzukiZ0 a K := (Subgroup.mem_comap).mp hy
    have hyy : y = ⟨s, h⟩ := Subtype.ext hys
    rwa [hyy] at hyZ
  have hS_sq_mem_X0 : ∀ s ∈ S, s ^ 2 ∈ X₀ := by
    intro s hs
    have hsLS : s ∈ L1 ⊔ S := Subgroup.mem_sup_right hs
    have hψs : ψ ⟨s, hsLS⟩ ∈ suzukiU a K := hψ_mem_U _ hs
    have hsq : ψ (⟨s, hsLS⟩ ^ 2) ∈ suzukiZ0 a K := by
      rw [map_pow]
      exact sq_mem_suzukiZ0 hK hψs
    exact Subgroup.mem_map_of_mem (L1 ⊔ S).subtype
      (show ⟨s, hsLS⟩ ^ 2 ∈ (suzukiZ0 a K).comap ψ from hsq)
  have hnotX0_sq_not_Q1 : ∀ s ∈ S, s ∉ X₀ → s ^ 2 ∉ Q1 L1 L2 S := by
    intro s hs hns hsq
    exact hns ((hmemX0 s).mpr ⟨hs, hsq⟩)
  have hsq_conj : ∀ s ∈ S, s ∉ X₀ → s ^ 2 ∈ X₀ ∧ s ^ 2 ∉ Q1 L1 L2 S :=
    fun s hs hns => ⟨hS_sq_mem_X0 s hs, hnotX0_sq_not_Q1 s hs hns⟩
  have hX0_normalized : bigB L1 L2 S ≤ normalizer (X₀ : Set G) := by
    intro b hb
    refine Subgroup.mem_normalizer_fintype ?_
    intro x hx
    change x ∈ X₀ at hx
    change b * x * b⁻¹ ∈ X₀
    rw [hmemX0] at hx ⊢
    obtain ⟨hxS, hx2⟩ := hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hB hb) x).mp hxS, ?_⟩
    have hbQ1 : b ∈ normalizer (Q1 L1 L2 S : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S) (Subgroup.mem_sup_right hb)
    have hsq : (b * x * b⁻¹) ^ 2 = b * x ^ 2 * b⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [hsq]
    exact (Subgroup.mem_normalizer_iff.mp hbQ1 (x ^ 2)).mp hx2
  have hnegpow : ζ ^ ((-1 : ZMod N).val) = ζ⁻¹ := by
    simpa [N] using pow_neg_one_val_eq_inv (n := 2 * a + 1) hζ (by simpa [N] using hNgt)
  have hlinv : ((l⁻¹ : Kˣ) : K) = ζ⁻¹ := by
    rw [Units.val_inv_eq_inv_val]
    rfl
  have hcenval : ((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) =
      ζ ^ ((-CFSG.Quasithin.Stroth.G5.cen (2 * a + 1)).val) := by
    rw [pow_cen_val_eq ha hζ, hlinv]
  let β : G → K := fun t => if h : t ∈ L1 ⊔ S then (szCoord (ψ ⟨t, h⟩)).1 else 0
  let β' : G → K := fun t => if h : t ∈ L1 ⊔ S then (szCoord (ψ ⟨t, h⟩)).2 else 0
  have hβ_apply : ∀ (t : G) (h : t ∈ L1 ⊔ S), β t = (szCoord (ψ ⟨t, h⟩)).1 := by
    intro t h
    simp only [β, dif_pos h]
  have hβ'_apply : ∀ (t : G) (h : t ∈ L1 ⊔ S), β' t = (szCoord (ψ ⟨t, h⟩)).2 := by
    intro t h
    simp only [β', dif_pos h]
  have hchiS : IsChiEmb₁ ζ d₁ X₀ S (-1) β := by
    refine ⟨?_, ?_, ?_⟩
    · intro s hs t ht
      have hsLS : s ∈ L1 ⊔ S := Subgroup.mem_sup_right hs
      have htLS : t ∈ L1 ⊔ S := Subgroup.mem_sup_right ht
      have hstLS : s * t ∈ L1 ⊔ S := (L1 ⊔ S).mul_mem hsLS htLS
      have hst : (⟨s * t, hstLS⟩ : ↥(L1 ⊔ S)) = ⟨s, hsLS⟩ * ⟨t, htLS⟩ := Subtype.ext rfl
      rw [hβ_apply (s * t) hstLS, hβ_apply s hsLS, hβ_apply t htLS, hst, map_mul]
      exact szCoord_mul_fst hK (hψ_mem_U _ hs) (hψ_mem_U _ ht)
    · intro s hs
      have hsLS : s ∈ L1 ⊔ S := Subgroup.mem_sup_right hs
      rw [hβ_apply s hsLS, szCoord_fst_eq_zero_iff hK (hψ_mem_U _ hs)]
      constructor
      · intro hZ
        exact Subgroup.mem_map_of_mem (L1 ⊔ S).subtype
          (show ⟨s, hsLS⟩ ∈ (suzukiZ0 a K).comap ψ from hZ)
      · intro hX
        obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp hX
        have hyZ : ψ y ∈ suzukiZ0 a K := (Subgroup.mem_comap).mp hy
        have hyy : y = ⟨s, hsLS⟩ := Subtype.ext hys
        rwa [hyy] at hyZ
    · intro s hs
      have hsLS : s ∈ L1 ⊔ S := Subgroup.mem_sup_right hs
      have hdsLS : d₁ * s * d₁⁻¹ ∈ L1 ⊔ S :=
        (L1 ⊔ S).mul_mem ((L1 ⊔ S).mul_mem d.2 hsLS) ((L1 ⊔ S).inv_mem d.2)
      rw [hβ_apply (d₁ * s * d₁⁻¹) hdsLS, hβ_apply s hsLS]
      have hsub : (⟨d₁ * s * d₁⁻¹, hdsLS⟩ : ↥(L1 ⊔ S)) = d * ⟨s, hsLS⟩ * d⁻¹ :=
        Subtype.ext rfl
      rw [hsub, map_mul, map_mul, map_inv, hψd,
        szCoord_conj_suzukiDElt hK l (hψ_mem_U _ hs)]
      change ((l⁻¹ : Kˣ) : K) * (szCoord (ψ ⟨s, hsLS⟩)).1 =
        ζ ^ ((-1 : ZMod N).val) * (szCoord (ψ ⟨s, hsLS⟩)).1
      have hnegpow' : ζ ^ ((-1 : ZMod N).val) = ((l⁻¹ : Kˣ) : K) := by
        rw [hnegpow, hlinv]
      rw [hnegpow']
  have hchiZ : IsChiEmb₁ ζ d₁ (Q1 L1 L2 S) X₀ (-CFSG.Quasithin.Stroth.G5.cen (2 * a + 1)) β' := by
    refine ⟨?_, ?_, ?_⟩
    · intro s hs t ht
      have hsLS : s ∈ L1 ⊔ S := Subgroup.mem_sup_right (hX0_le_S hs)
      have htLS : t ∈ L1 ⊔ S := Subgroup.mem_sup_right (hX0_le_S ht)
      have hstLS : s * t ∈ L1 ⊔ S := (L1 ⊔ S).mul_mem hsLS htLS
      have hst : (⟨s * t, hstLS⟩ : ↥(L1 ⊔ S)) = ⟨s, hsLS⟩ * ⟨t, htLS⟩ := Subtype.ext rfl
      rw [hβ'_apply (s * t) hstLS, hβ'_apply s hsLS, hβ'_apply t htLS, hst, map_mul]
      exact szCoord_mul_snd hK (hX0_Z s hs hsLS) (hX0_Z t ht htLS)
    · intro s hs
      have hsLS : s ∈ L1 ⊔ S := Subgroup.mem_sup_right (hX0_le_S hs)
      rw [hβ'_apply s hsLS, szCoord_snd_eq_zero_iff hK (hX0_Z s hs hsLS)]
      constructor
      · intro h1
        have h2 : e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) ⟨s, hsLS⟩) = 1 := by
          simpa [ψ] using h1
        have h3 : QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) ⟨s, hsLS⟩ = 1 :=
          e.injective (by rw [map_one]; exact h2)
        have hmem : (⟨s, hsLS⟩ : ↥(L1 ⊔ S)) ∈ pCore 2 ↥(L1 ⊔ S) :=
          (QuotientGroup.eq_one_iff _).mp h3
        have h := (CFSG.Quasithin.F1.mem_pCore_iff_coe (⟨s, hsLS⟩ : ↥(L1 ⊔ S))).mp hmem
        rwa [hpCore] at h
      · intro hq
        have hmem : (⟨s, hsLS⟩ : ↥(L1 ⊔ S)) ∈ pCore 2 ↥(L1 ⊔ S) := by
          refine (CFSG.Quasithin.F1.mem_pCore_iff_coe _).mpr ?_
          rw [hpCore]
          exact hq
        have h1 : QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) ⟨s, hsLS⟩ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hmem
        rw [show ψ ⟨s, hsLS⟩ =
          e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) ⟨s, hsLS⟩) from rfl, h1, map_one]
    · intro s hs
      have hsLS : s ∈ L1 ⊔ S := Subgroup.mem_sup_right (hX0_le_S hs)
      have hdsLS : d₁ * s * d₁⁻¹ ∈ L1 ⊔ S :=
        (L1 ⊔ S).mul_mem ((L1 ⊔ S).mul_mem d.2 hsLS) ((L1 ⊔ S).inv_mem d.2)
      rw [hβ'_apply (d₁ * s * d₁⁻¹) hdsLS, hβ'_apply s hsLS]
      have hsub : (⟨d₁ * s * d₁⁻¹, hdsLS⟩ : ↥(L1 ⊔ S)) = d * ⟨s, hsLS⟩ * d⁻¹ :=
        Subtype.ext rfl
      rw [hsub, map_mul, map_mul, map_inv, hψd,
        szCoord_conj_suzukiDElt hK l (suzukiZ0_le_suzukiU (hX0_Z s hs hsLS))]
      change ((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * (szCoord (ψ ⟨s, hsLS⟩)).2 =
        ζ ^ ((-CFSG.Quasithin.Stroth.G5.cen (2 * a + 1)).val) *
          (szCoord (ψ ⟨s, hsLS⟩)).2
      rw [hcenval]
  refine ⟨d₁, X₀, β, β', hzpow, horder, hQ1_le_X0, hX0_le_S, hX0_normalized,
    hsq_conj, hchiS, hchiZ⟩

end
