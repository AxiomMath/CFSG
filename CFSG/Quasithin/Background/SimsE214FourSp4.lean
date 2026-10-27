module

public import CFSG.Quasithin.Background.SimsE214FourSz
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ1

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp uElt antiUnipotent
  antiUnipotentCenter)

namespace E214F

theorem exists_c2_of_isSp4Full {Y : Type} [Group Y] [Finite Y] {k : ℕ} (hY : IsSp4Full k Y)
    {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) :
    ∃ w ∈ S ⊓ Subgroup.centralizer (S : Set Y), Subgroup.centralizer ({w} : Set Y) ≤ S := by
  obtain ⟨K, _, _, _, -, ⟨φ⟩⟩ := E213M.exists_antiSp_of_isSp4Full hY
  have hU := (CFSG.QuasithinUnique.Setup.X7b.card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  have hS' : IsSylowTwoOf (S.map φ.toMonoidHom) ⊤ := E2.isSylowTwoOf_map_equiv φ hS
  obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj hU hS'
  set z₀ : antiSp K := uElt 0 1 1 0 with hz₀
  have hz₀Z : z₀ ∈ antiUnipotentCenter K := ⟨1, 1, rfl⟩
  have hz₀U := ((CFSG.QuasithinUnique.Setup.X7b.mem_antiUnipotentCenter_iff_central z₀).mp hz₀Z)
  have hmemS : ∀ x : Y, x ∈ S ↔ c⁻¹ * φ x * c ∈ antiUnipotent K := by
    intro x
    rw [← B6.mem_conjSub, ← hc, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  set w := φ.symm (c * z₀ * c⁻¹) with hw
  have hφw : φ w = c * z₀ * c⁻¹ := MulEquiv.apply_symm_apply _ _
  have hwS : w ∈ S := by
    rw [hmemS, hφw]
    have e1 : c⁻¹ * (c * z₀ * c⁻¹) * c = z₀ := by group
    rw [e1]
    exact hz₀U.1
  refine ⟨w, Subgroup.mem_inf.mpr ⟨hwS, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩, ?_⟩
  · apply φ.injective
    rw [map_mul, map_mul, hφw]
    have h1 := hz₀U.2 _ ((hmemS s).mp hs)
    calc φ s * (c * z₀ * c⁻¹) = c * ((c⁻¹ * φ s * c) * z₀) * c⁻¹ := by group
      _ = c * (z₀ * (c⁻¹ * φ s * c)) * c⁻¹ := by rw [h1]
      _ = c * z₀ * c⁻¹ * φ s := by group
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [hmemS]
    refine CFSG.Quasithin.Ch3E213M.G41.CTwo.mem_antiUnipotent_of_comm one_ne_zero one_ne_zero ?_
    have h1 := congrArg φ hx
    rw [map_mul, map_mul, hφw] at h1
    calc c⁻¹ * φ x * c * uElt 0 1 1 0 = c⁻¹ * (φ x * (c * z₀ * c⁻¹)) * c := by rw [hz₀]; group
      _ = c⁻¹ * ((c * z₀ * c⁻¹) * φ x) * c := by rw [h1]
      _ = uElt 0 1 1 0 * (c⁻¹ * φ x * c) := by rw [hz₀]; group

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem center_eq_bot_of_le {X T M V : Subgroup Γ} {g : Γ} (hp : E2.Pair X T M V g)
    {S : Subgroup (E2.StarQuot M X)} (hS : IsPGroup 2 S)
    (hZS : Subgroup.center (E2.StarQuot M X) ≤ S) : Subgroup.center (E2.StarQuot M X) = ⊥ := by
  set π := E2P.starMap M X with hπ
  set D : Subgroup Γ := ((Subgroup.center (E2.StarQuot M X)).comap π).map X.subtype with hD
  have hmemD : ∀ y : Γ, y ∈ D ↔ ∃ hy : y ∈ X, π ⟨y, hy⟩ ∈ Subgroup.center (E2.StarQuot M X) := by
    intro y
    rw [hD, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hDX : D ≤ X := fun y hy => ((hmemD y).mp hy).1
  have hXD : X ≤ Subgroup.normalizer (D : Set Γ) := by
    have key : ∀ i ∈ X, ∀ y ∈ D, i * y * i⁻¹ ∈ D := by
      intro i hi y hy
      obtain ⟨hyX, hyc⟩ := (hmemD y).mp hy
      refine (hmemD _).mpr ⟨X.mul_mem (X.mul_mem hi hyX) (X.inv_mem hi), ?_⟩
      have e1 : (⟨i * y * i⁻¹, X.mul_mem (X.mul_mem hi hyX) (X.inv_mem hi)⟩ : X) =
          ⟨i, hi⟩ * ⟨y, hyX⟩ * (⟨i, hi⟩ : X)⁻¹ := rfl
      have hc := Subgroup.mem_center_iff.mp hyc (π ⟨i, hi⟩)
      rw [e1, map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
      exact hyc
    exact fun i hi => B6.mem_normalizer_of_forall_mem (key i hi)
      (fun y hy => by simpa using key i⁻¹ (X.inv_mem hi) y hy)
  have hJD : kerIn M X ≤ D := by
    intro j hj
    have hjX : j ∈ X := hp.le_X (kerIn_le hj)
    refine (hmemD j).mpr ⟨hjX, ?_⟩
    have h1 : π ⟨j, hjX⟩ = 1 := by
      rw [hπ, E2P.starMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      exact hj
    rw [h1]
    exact Subgroup.one_mem _
  have h2 : ∀ d ∈ D, ∃ n : ℕ, d ^ 2 ^ n ∈ kerIn M X := by
    intro d hd
    obtain ⟨hdX, hdc⟩ := (hmemD d).mp hd
    obtain ⟨n, hn⟩ := hS ⟨_, hZS hdc⟩
    refine ⟨n, ?_⟩
    have h3 : π (⟨d, hdX⟩ ^ 2 ^ n) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hn
    rw [hπ, E2P.starMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h3
    simpa using h3
  have hDJ := hp.le_kerIn_of_isTwoQuotient hDX hXD hJD h2
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn M X).subgroupOf X) z
  have hxD : (x : Γ) ∈ D := (hmemD x).mpr ⟨x.2, hz⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  exact hDJ hxD

theorem mem_of_normal_of_perm_six {Y : Type*} [Group Y] (e : Y ≃* Equiv.Perm (Fin 6))
    {N : Subgroup Y} (hN : N.Normal) (hN1 : N ≠ ⊥) {z : Y} (hz : Odd (orderOf z)) : z ∈ N := by
  have hN' : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
  have hne : N.map e.toMonoidHom ≠ ⊥ := by
    intro h0
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ N.map e.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rw [h0, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  have hnt : Nontrivial ↥(N.map e.toMonoidHom) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hA := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp)
    (N := N.map e.toMonoidHom) hnt
  have hsign : Equiv.Perm.sign (e z) = 1 := by
    have hord : Odd (orderOf (e z)) := by rw [MulEquiv.orderOf_eq]; exact hz
    have h1 : Equiv.Perm.sign (e z) ^ orderOf (e z) = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (e z)) with h2 | h2
    · exact h2
    · rw [h2, hord.neg_one_pow] at h1
      exact absurd h1 (by decide)
  have h3 : e z ∈ N.map e.toMonoidHom := hA (Equiv.Perm.mem_alternatingGroup.mpr hsign)
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h3
  exact h3

theorem four_of_sp4
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) {k : ℕ} (hk : 1 ≤ k)
    (hSp : IsSp4Full k (E2.StarQuot (M ⊓ I) I))
    (hVeq : E2.star (M ⊓ I) I V = ASInputs.e214ZT T M I)
    {Y₁ Y₂ : Subgroup Γ} (hZY : V ⊓ conjSubgroup V g ≤ Y₂) (hY : Y₂ < Y₁)
    (hY₁P : Y₁ ≤ (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I))
    (hIY₁ : I ≤ Subgroup.normalizer (Y₁ : Set Γ))
    (hIY₂ : I ≤ Subgroup.normalizer (Y₂ : Set Γ)) :
    4 * k ≤ E3.mQuot Y₁ Y₂ := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := e ▸ hIV
  obtain ⟨hp, -, -, -, hJ, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) hgen
  set S := E2.star (M ⊓ I) I (T ⊓ I) with hSdef
  have hS : IsSylowTwoOf S ⊤ := E2.isSylowTwoOf_star_inf (M := M) hp.sylow
  obtain ⟨w, hwZ, hCw⟩ := exists_c2_of_isSp4Full hSp hS
  have hwV : w ∈ E2.star (M ⊓ I) I V := hVeq ▸ hwZ
  rw [E2P.star_def] at hwV
  obtain ⟨⟨v, hvI⟩, hvV, rfl⟩ := Subgroup.mem_map.mp hwV
  have hv : v ∈ V := Subgroup.mem_subgroupOf.mp hvV
  have hcen : Subgroup.center (E2.StarQuot (M ⊓ I) I) = ⊥ := by
    refine center_eq_bot_of_le hp hS.2.1 fun z hz => hCw ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hz _).symm
  have he : g⁻¹ * v * g⁻¹⁻¹ ∈ B6.conjSub g⁻¹ V := by
    rw [B6.mem_conjSub]
    simpa [mul_assoc] using hv
  obtain ⟨hgv, hge⟩ := gen_of_centralizer_le hp hcen hVeq hv hCw he
  obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * k) (by omega)
    (by omega)
  have hrX : r ∣ Nat.card (E2.StarQuot (M ⊓ I) I) :=
    (Ch3E213M.primitive_dvd_sq_add_one hk hr).trans (E213M.sq_add_one_dvd_card hSp)
  have hN : ∀ N : Subgroup (E2.StarQuot (M ⊓ I) I), N.Normal → N ≠ ⊥ →
      ∀ z : E2.StarQuot (M ⊓ I) I, Odd (orderOf z) → z ∈ N := by
    intro N hNn hN1 z hz
    rcases hSp with hPSp | ⟨-, ⟨e6⟩⟩
    · have hs := E2.isSimpleGroup_of_isPSp4 hPSp
      rcases hNn.eq_bot_or_eq_top with h0 | h0
      · exact absurd h0 hN1
      · rw [h0]
        exact Subgroup.mem_top z
    · exact mem_of_normal_of_perm_six e6 hNn hN1 hz
  have hPeq : (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I) =
      (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) := by
    rw [e, hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm]
  exact four_of_gen hp hJ hN (by omega) hr hrX hv he hgv hge (e ▸ hZY) hY (hPeq ▸ hY₁P)
    hIY₁ hIY₂

end E214F

end CFSG.Quasithin.SimsE2
