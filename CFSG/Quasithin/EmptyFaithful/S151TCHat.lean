module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitHatA6
public import CFSG.Quasithin.Background.SmithB42HatA6Model
public import CFSG.Quasithin.EmptyFaithful.S151TBMain
public import CFSG.Quasithin.EmptyFaithful.S151TCOrd
public import CFSG.Quasithin.EmptyFaithful.S151TCA6
public import CFSG.Quasithin.EmptyFaithful.S151TCFlag
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.H13.Orbit CFSG.Quasithin.HatA6 CFSG.Quasithin.S151TB


@[expose] def matAut {F : Type} [Field F] (g : Matrix.GeneralLinearGroup (Fin 3) F) :
    MulAut (Multiplicative (Fin 3 → F)) where
  toFun v := Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd
    (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
      (Multiplicative.toAdd v))
  left_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    have : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
    rfl
  right_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    have : (g : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
    rfl
  map_mul' a b := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem matAut_apply {F : Type} [Field F] (g : Matrix.GeneralLinearGroup (Fin 3) F)
    (v : Multiplicative (Fin 3 → F)) :
    matAut g v =
      Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd v)) :=
  rfl

@[expose] def matAutHom (F : Type) [Field F] :
    Matrix.GeneralLinearGroup (Fin 3) F →* MulAut (Multiplicative (Fin 3 → F)) where
  toFun := matAut
  map_one' := by
    ext v
    simp [matAut_apply]
  map_mul' a b := by
    ext v
    simp [matAut_apply, Matrix.mulVec_mulVec]

theorem matAutHom_injective (F : Type) [Field F] : Function.Injective (matAutHom F) := by
  intro a b hab
  have h : ∀ v : Fin 3 → F, (a : Matrix (Fin 3) (Fin 3) F).mulVec v =
      (b : Matrix (Fin 3) (Fin 3) F).mulVec v := by
    intro v
    have := congrArg (fun φ : MulAut (Multiplicative (Fin 3 → F)) =>
      Multiplicative.toAdd (φ (Multiplicative.ofAdd v))) hab
    simpa [matAutHom, matAut_apply] using this
  apply Units.ext
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v



theorem fpf_of_center_generator {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {zH : ↥H}
    (hzc : Subgroup.center ↥H = Subgroup.zpowers zH) (hz3 : (zH : MulAut V) ^ 3 = 1)
    (hzf : ∀ v : V, (zH : MulAut V) v = v → v = 1) :
    ∀ z ∈ Subgroup.center ↥H, z ≠ 1 → ∀ v : V, (z : MulAut V) v = v → v = 1 := by
  intro z hz hz1 v hv
  rw [hzc] at hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hz3' : zH ^ 3 = 1 := Subtype.ext hz3
  have hzH1 : zH ≠ 1 := by
    rintro rfl
    exact hz1 (one_zpow k)
  have hord : orderOf zH = 3 := orderOf_eq_prime hz3' hzH1
  have hk : zH ^ k = zH ^ (k % 3) := by
    have := zpow_mod_orderOf zH k
    rw [hord] at this
    exact this.symm
  have hk' : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hk3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rw [hk] at hv hz1
  generalize k % 3 = m at hv hz1 hk' hk3
  interval_cases m
  · exact absurd (by simp) hz1
  · exact hzf v (by simpa using hv)
  · have hv' : (zH : MulAut V) ((zH : MulAut V) v) = v := by
      have h2 : (zH ^ (2 : ℤ) : ↥H) = zH * zH := by rw [zpow_two]
      rw [h2] at hv
      exact hv
    have h5 : (zH : MulAut V) * (zH : MulAut V) * (zH : MulAut V) = 1 := by
      have : (zH : MulAut V) ^ 3 = 1 := hz3
      simpa [pow_succ, mul_assoc] using this
    have h6 : (zH : MulAut V) ((zH : MulAut V) ((zH : MulAut V) v)) = v := by
      have := congrArg (fun φ : MulAut V => φ v) h5
      simpa using this
    have h7 : (zH : MulAut V) ((zH : MulAut V) ((zH : MulAut V) v)) = (zH : MulAut V) v :=
      congrArg (zH : MulAut V) hv'
    exact hzf v (h7.symm.trans h6)

theorem hatA6_core {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {Γ : Type} [Group Γ] [Finite Γ] (ρ : Γ →* Matrix.GeneralLinearGroup (Fin 3) F)
    (hρ : Function.Injective ρ) (hperf : Group.IsPerfect Γ)
    (hZ : Nat.card (Subgroup.center Γ) = 3)
    (e : Γ ⧸ Subgroup.center Γ ≃* alternatingGroup (Fin 6))
    (D : Subgroup Γ) (hD8 : Nat.card D = 8)
    (w₀ : Fin 3 → F) (hw₀ : w₀ ≠ 0)
    (hDw : ∀ d ∈ D, (ρ d : Matrix (Fin 3) (Fin 3) F).mulVec w₀ = w₀)
    (W : Submodule F (Fin 3 → F)) (hW : Module.finrank F W = 2)
    (hTW : ∀ g : Γ, (ρ g : Matrix (Fin 3) (Fin 3) F).mulVec w₀ = w₀ →
      ∀ w ∈ W, (ρ g : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W) : False := by
  classical
  have hcharF : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [hF]; norm_num)
  have hV : Nat.card (Multiplicative (Fin 3 → F)) = 2 ^ 6 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_pi]
    simp [hF]
  have hsq : ∀ v : Multiplicative (Fin 3 → F), v ^ 2 = 1 := by
    intro v
    ext i
    simp [pow_two, CharTwo.add_self_eq_zero]
  let ψ : Γ →* MulAut (Multiplicative (Fin 3 → F)) := (matAutHom F).comp ρ
  have hψ : Function.Injective ψ := (matAutHom_injective F).comp hρ
  let H : Subgroup (MulAut (Multiplicative (Fin 3 → F))) := ψ.range
  let eΓH : Γ ≃* H := MonoidHom.ofInjective hψ
  have hHperf : Group.IsPerfect ↥H :=
    Group.IsPerfect.ofSurjective (f := eΓH.toMonoidHom) eΓH.surjective
  have hHcen : (Subgroup.center Γ).map eΓH.toMonoidHom = Subgroup.center ↥H :=
    Subgroup.map_center_eq eΓH
  have hHZ : Nat.card (Subgroup.center ↥H) = 3 := by
    have h1 : Nat.card (Subgroup.center ↥H) =
        Nat.card ((Subgroup.center Γ).map eΓH.toMonoidHom) := by rw [hHcen]
    rw [h1, Subgroup.card_map_of_injective (f := eΓH.toMonoidHom) eΓH.injective]
    exact hZ
  have eH : ↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr (Subgroup.center Γ) (Subgroup.center ↥H) eΓH hHcen).symm.trans e.symm.symm
  have hV' : Nat.card (Multiplicative (Fin 3 → F)) = 64 := by rw [hV]; norm_num
  obtain ⟨zH, hzc, hz3, hzf⟩ := exists_center_fpf hsq hV hHperf hHZ eH
  have hfpf := fpf_of_center_generator hzc hz3 hzf
  obtain ⟨f, hf1, hf⟩ := hatA6_orbits hV' (Group.isPerfect_def.1 hHperf) hHZ eH hfpf
  set v0 : Multiplicative (Fin 3 → F) := Multiplicative.ofAdd w₀ with hv0def
  have hv0 : v0 ≠ 1 := by
    intro h
    apply hw₀
    simpa [hv0def] using congrArg Multiplicative.toAdd h
  have hcard1845 : Nat.card (orbitIn H v0) = 18 ∨ Nat.card (orbitIn H v0) = 45 := by
    by_cases h : v0 ∈ orbitIn H f
    · exact Or.inl ((hf v0 hv0).1 h)
    · exact Or.inr ((hf v0 hv0).2 h)
  let _ : MulAction Γ (Multiplicative (Fin 3 → F)) := MulAction.compHom _ ψ
  have hsmul : ∀ (g : Γ) (v : Multiplicative (Fin 3 → F)), g • v = ψ g v := fun _ _ => rfl
  have horb : MulAction.orbit Γ v0 = orbitIn H v0 := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨ψ g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨h, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  set T : Subgroup Γ := MulAction.stabilizer Γ v0 with hTdef
  have hTmem : ∀ g : Γ, g ∈ T ↔ (ρ g : Matrix (Fin 3) (Fin 3) F).mulVec w₀ = w₀ := by
    intro g
    rw [hTdef, MulAction.mem_stabilizer_iff, hsmul]
    constructor
    · intro h
      simpa [ψ, matAutHom, matAut_apply, hv0def] using congrArg Multiplicative.toAdd h
    · intro h
      simp [ψ, matAutHom, matAut_apply, hv0def, h]
  have hΓ : Nat.card Γ = 1080 := (quasisimple_card hperf hZ e).2
  have hos : Nat.card (orbitIn H v0) * Nat.card T = 1080 := by
    rw [← horb, ← hΓ, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact T.index_mul_card
  have hDT : D ≤ T := fun d hd => (hTmem d).2 (hDw d hd)
  have h8T : 8 ∣ Nat.card T := hD8 ▸ Subgroup.card_dvd_of_le hDT
  have hT24 : Nat.card T = 24 := by
    rcases hcard1845 with h | h
    · rw [h] at hos
      have : Nat.card T = 60 := by omega
      rw [this] at h8T
      omega
    · rw [h] at hos
      omega
  have hTZ : T ⊓ Subgroup.center Γ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgT, hgZ⟩
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hgH : (eΓH g : ↥H) ∈ Subgroup.center ↥H := by
      rw [← hHcen]
      exact ⟨g, hgZ, rfl⟩
    have hne : (eΓH g : ↥H) ≠ 1 := fun h => hg1 (eΓH.injective (h.trans (map_one eΓH).symm))
    have hstab : g • v0 = v0 := MulAction.mem_stabilizer_iff.1 hgT
    have := hfpf _ hgH hne v0 (by
      have h2 : ((eΓH g : ↥H) : MulAut (Multiplicative (Fin 3 → F))) v0 = g • v0 := rfl
      rw [h2]
      exact hstab)
    exact hv0 this
  obtain ⟨N, hNT, hN8, hNn⟩ := flag_normal_subgroup hF ρ hρ T hT24 w₀ hw₀
    (fun t ht => (hTmem t).1 ht) W hW (fun t ht => hTW t ((hTmem t).1 ht))
  have := eq_of_normal_of_inf_center_eq_bot e hN8 hNT hTZ hNn
  rw [this] at hT24
  omega

theorem mem_pCoreOf_iff_mem_pCore' {G : Type} [Group G] {X : Subgroup G} (x : X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff x

theorem le_normalizer_blockU {G : Type} [Group G] [Finite G] (L : Subgroup G) :
    L ≤ Subgroup.normalizer (blockU L : Set G) := fun _ hx =>
  normalizer_commutator (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hx)
    (Subgroup.le_normalizer hx)

section Application

theorem exists_sylow_of_isSylowTwoOf' {G : Type} [Group G] {S H : Subgroup G}
    (hS : IsSylowTwoOf S H) : ∃ P : Sylow 2 ↥H, (P : Subgroup ↥H) = S.subgroupOf H := by
  obtain ⟨hSH, hp, hidx⟩ := hS
  have hp' : IsPGroup 2 ↥(S.subgroupOf H) :=
    hp.of_injective (Subgroup.subgroupOfEquivOfLe hSH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSH).injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hp'.toSylow hidx, IsPGroup.toSylow_coe _ _⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {F : Type} [Field F]

theorem ker_eq_pCore_of_equivariant
    (hcent : L ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 L)
    (ρ : ↥L →* Matrix.GeneralLinearGroup (Fin 3) F)
    (e : ↥(blockU L) ≃* Multiplicative (Fin 3 → F))
    (hequiv : ∀ (k : ↥L) (u v : ↥(blockU L)), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (e v) =
        ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (e u))) :
    ρ.ker = CFSG.pCore 2 ↥L := by
  ext k
  rw [MonoidHom.mem_ker, ← mem_pCoreOf_iff_mem_pCore', ← hcent]
  have hconj : ∀ u : ↥(blockU L), k * (u : G) * (k : G)⁻¹ ∈ blockU L := fun u =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_blockU L k.2) u).1 u.2
  constructor
  · intro h1
    refine ⟨k.2, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    have := hequiv k ⟨u, hu⟩ ⟨(k : G) * u * (k : G)⁻¹, hconj ⟨u, hu⟩⟩ rfl
    rw [h1] at this
    simp only [Units.val_one, Matrix.one_mulVec] at this
    have h2 := e.injective (Multiplicative.toAdd.injective this)
    have h3 : (k : G) * u * (k : G)⁻¹ = u := congrArg Subtype.val h2
    calc u * (k : G) = ((k : G) * u * (k : G)⁻¹) * (k : G) := by rw [h3]
      _ = (k : G) * u := by group
  · rintro ⟨-, hk⟩
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, hu⟩ := e.surjective (Multiplicative.ofAdd x)
    have h3 : (k : G) * u * (k : G)⁻¹ = u := by
      have := Subgroup.mem_centralizer_iff.1 hk u u.2
      calc (k : G) * u * (k : G)⁻¹ = ((u : G) * k) * (k : G)⁻¹ := by rw [this]
        _ = u := by group
    have := hequiv k u ⟨(k : G) * u * (k : G)⁻¹, hconj u⟩ rfl
    have h4 : (⟨(k : G) * u * (k : G)⁻¹, hconj u⟩ : ↥(blockU L)) = u := Subtype.ext h3
    rw [h4, hu] at this
    simpa [Matrix.toLin'_apply] using this.symm

theorem hat_contra {SL : Subgroup G}
    (hq : CFSG.IsQuasisimple (LStar L)) (hZ3 : Nat.card (Subgroup.center (LStar L)) = 3)
    (eA : LStar L ⧸ Subgroup.center (LStar L) ≃* alternatingGroup (Fin 6))
    (hcent : L ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 L)
    (hSyl : IsSylowTwoOf SL L) [Fintype F] (hF4 : Fintype.card F = 4)
    (ρ : ↥L →* Matrix.GeneralLinearGroup (Fin 3) F)
    (e : ↥(blockU L) ≃* Multiplicative (Fin 3 → F))
    (hequiv : ∀ (k : ↥L) (u v : ↥(blockU L)), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (e v) =
        ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (e u)))
    (W : Submodule F (Fin 3 → F)) (hW2 : Module.finrank F W = 2)
    (w : G) (hwU : w ∈ blockU L) (hw1 : w ≠ 1) (hwfix : ∀ s ∈ SL, s * w * s⁻¹ = w)
    (hWst : ∀ k : ↥L, (k : G) * w = w * k → ∀ w' ∈ W,
      ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w' ∈ W) :
    False := by
  classical
  have hker := ker_eq_pCore_of_equivariant hcent ρ e hequiv
  set N : Subgroup ↥L := CFSG.pCore 2 ↥L with hNdef
  have : N.Normal := CFSG.pCore_normal
  let ρb : LStar L →* Matrix.GeneralLinearGroup (Fin 3) F :=
    QuotientGroup.lift N ρ (by rw [← hker])
  have hρb_mk : ∀ k : ↥L, ρb (QuotientGroup.mk k) = ρ k := fun k => rfl
  have hρb : Function.Injective ρb := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hρb_mk, hρb_mk] at hxy
    rw [QuotientGroup.eq]
    show a⁻¹ * b ∈ N
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  set u0 : ↥(blockU L) := ⟨w, hwU⟩ with hu0
  set w₀ : Fin 3 → F := Multiplicative.toAdd (e u0) with hw₀def
  have hw₀ : w₀ ≠ 0 := by
    intro h
    have h1 : e u0 = 1 := by
      apply Multiplicative.toAdd.injective
      simpa [hw₀def] using h
    have h2 : u0 = 1 := e.injective (h1.trans (map_one e).symm)
    exact hw1 (congrArg Subtype.val h2)
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf' hSyl
  have hcard : Nat.card (LStar L) = 1080 := (quasisimple_card hq.1 hZ3 eA).2
  let Pb : Sylow 2 (LStar L) := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have hPb : (Pb : Subgroup (LStar L)) = (P : Subgroup ↥L).map (QuotientGroup.mk' N) :=
    P.coe_mapSurjective _
  have hfixD : ∀ x ∈ (Pb : Subgroup (LStar L)),
      (ρb x : Matrix (Fin 3) (Fin 3) F).mulVec w₀ = w₀ := by
    intro x hx
    rw [hPb] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyS : (y : G) ∈ SL := by
      have := hP ▸ hy
      exact (Subgroup.mem_subgroupOf.1 this)
    have := hequiv y u0 ⟨(y : G) * w * (y : G)⁻¹, (Subgroup.mem_normalizer_iff.1
      (le_normalizer_blockU L y.2) w).1 hwU⟩ rfl
    have h2 : (⟨(y : G) * w * (y : G)⁻¹, (Subgroup.mem_normalizer_iff.1
        (le_normalizer_blockU L y.2) w).1 hwU⟩ : ↥(blockU L)) = u0 :=
      Subtype.ext (hwfix y hyS)
    rw [h2] at this
    exact this.symm
  have hD8 : Nat.card (Pb : Subgroup (LStar L)) = 8 := by
    rw [Sylow.card_eq_multiplicity, hcard]
    norm_num [Nat.factorization]
  have hTW : ∀ g : LStar L, (ρb g : Matrix (Fin 3) (Fin 3) F).mulVec w₀ = w₀ →
      ∀ w' ∈ W, (ρb g : Matrix (Fin 3) (Fin 3) F).mulVec w' ∈ W := by
    intro g hg w' hw'
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hρb_mk] at hg ⊢
    refine hWst k ?_ w' hw'
    have hmem : (k : G) * w * (k : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_blockU L k.2) w).1 hwU
    have := hequiv k u0 ⟨(k : G) * w * (k : G)⁻¹, hmem⟩ rfl
    rw [hg] at this
    have h2 : (⟨(k : G) * w * (k : G)⁻¹, hmem⟩ : ↥(blockU L)) = u0 :=
      e.injective (Multiplicative.toAdd.injective this)
    have h3 : (k : G) * w * (k : G)⁻¹ = w := congrArg Subtype.val h2
    calc (k : G) * w = ((k : G) * w * (k : G)⁻¹) * (k : G) := by group
      _ = w * k := by rw [h3]
  exact hatA6_core hF4 ρb hρb hq.1 hZ3 eA (Pb : Subgroup (LStar L)) hD8 w₀ hw₀ hfixD W hW2 hTW

end Application

section Top

variable {G : Type} [Group G] [Finite G] {L T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}

theorem exists_fixed_vec (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hchar : CharTwo L)
    (hcomp : L ∈ cComp (g1_1516 Z₁)) (hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G)) :
    ∃ w ∈ blockU L, w ≠ 1 ∧ (∀ s ∈ s1516 T Z₁ ⊓ L, s * w * s⁻¹ = w) ∧
      ∀ l ∈ L, l * w = w * l → l ∈ mZ1516 Mc Z₁ := by
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hcomp
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hB : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := sylow_inf hc
  have hS2 : IsPGroup 2 ↥(s1516 T Z₁) := hc.h18.four.2.1
  obtain ⟨W, hWb, hWfix, -, hWz⟩ := exists_zU hchar hperf hS2 hSN hB (omegaOneCenter_le hc)
  have hnot := not_le_centralizer hc hLG
  obtain ⟨l₀, hl₀L, hl₀⟩ : ∃ l ∈ L, l ∉ Subgroup.centralizer
      (quasithinOmegaOneCenter T : Set G) := by
    by_contra h
    push Not at h
    exact hnot h
  rw [Subgroup.mem_centralizer_iff] at hl₀
  push Not at hl₀
  obtain ⟨z, hz, hl₀z⟩ := hl₀
  obtain ⟨w, hw, hwiff⟩ := hWz z hz
  have hz1 : z ≠ 1 := by
    intro h
    apply hl₀z
    rw [h]
    simp
  refine ⟨w, hWb hw, ?_, hWfix w hw, fun l hl hlw => ?_⟩
  · rintro rfl
    apply hl₀z
    exact ((hwiff l₀ hl₀L).2 (by simp)).symm
  · exact centralizer_le_mZ hc hz hz1 (hLG hl) ((hwiff l hl).2 hlw)

theorem input15120NoHatA6_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) :
    S151TB.Input15120NoHatA6 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hHat
  obtain ⟨-, hhat, -, hcent⟩ := hHat
  have hq : CFSG.IsQuasisimple (LStar L) := hc.hL.quasi
  obtain ⟨-, hZ3, ⟨eA⟩⟩ := hhat
  have hD : ListD' L := Or.inr (Or.inl ⟨eA⟩)
  have hN := g1_le_normalizer h37 h38 hc hcomp hD
  have hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    (q1_1516_le Mc Z₁).trans ((mZ1516_le_g1 Mc Z₁).trans hN)
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := (s1516_le_g1 T Z₁).trans hN
  have hcard : Nat.card (LStar L) = 1080 := (quasisimple_card hq.1 hZ3 eA).2
  obtain ⟨-, -, F, _, _, hF4, ρ, e, hequiv, W, hW2, hWM⟩ :=
    c27_c_of_card1080 (hC27 G) hc.h18.five.2.2 hcomp hq hchar hc.hL.not_le hRN hcard
  obtain ⟨w, hwU, hw1, hwfix, hwM⟩ := exists_fixed_vec hc hchar hcomp hSN
  exact hat_contra hq hZ3 eA hcent (sylow_inf hc) hF4 ρ e hequiv W hW2 w hwU hw1 hwfix
    (fun k hk w' hw' => (hWM k).1 (hwM k k.2 hk) w' hw')

end Top

end CFSG.Quasithin.S151TC
