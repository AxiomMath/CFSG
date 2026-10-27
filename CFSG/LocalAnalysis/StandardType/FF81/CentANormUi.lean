module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAFrame
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.StandardType.FF81.CentAO2
import CFSG.LocalAnalysis.StandardType.FF81.CentAInvariant
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelPara
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelUnip

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin CFSG.Open

variable {G : Type} [Group G] [Finite G] {m : ℕ} {Y L R : Subgroup G} {b t : G}
  {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}

private theorem caNormU_t_mem_liftSub (hS : CentASetting m Y L R b t φ)
    {K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))} (hJ : jGL 1 m ∈ K) :
    t ∈ liftSub φ K := by
  refine (mem_liftSub (K := K)).mpr ⟨hS.t_mem, ?_⟩
  rw [hS.φ_t]
  exact hJ

private theorem caNormU_conj_mem_liftSub (hS : CentASetting m Y L R b t φ)
    {K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))}
    (hKn : ∀ g ∈ Cent 1 m, ∀ u ∈ K, g * u * g⁻¹ ∈ K)
    {y u : G} (hy : y ∈ liftSub φ (Cent 1 m)) (hu : u ∈ liftSub φ K) :
    y * u * y⁻¹ ∈ liftSub φ K := by
  obtain ⟨hyY, hyC⟩ := (mem_liftSub (K := Cent 1 m)).mp hy
  obtain ⟨huY, huK⟩ := (mem_liftSub (K := K)).mp hu
  have hmem : y * u * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hyY huY) (Y.inv_mem hyY)
  refine (mem_liftSub (K := K)).mpr ⟨hmem, ?_⟩
  have heq : (⟨y * u * y⁻¹, hmem⟩ : ↥Y) = ⟨y, hyY⟩ * ⟨u, huY⟩ * ⟨y, hyY⟩⁻¹ := by
    ext
    simp
  rw [heq, map_mul, map_mul, map_inv]
  exact hKn (φ ⟨y, hyY⟩) hyC (φ ⟨u, huY⟩) huK

private theorem caNormU_mul_self_eq_one_of_mem_liftSub
    (hS : CentASetting m Y L R b t φ)
    {K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))} (hKexp : ∀ u ∈ K, u * u = 1)
    {u : G} (hu : u ∈ liftSub φ K) : u * u = 1 := by
  obtain ⟨huY, huK⟩ := (mem_liftSub (K := K)).mp hu
  have hmem : u * u ∈ Y := Y.mul_mem huY huY
  have hφ : φ ⟨u * u, hmem⟩ = 1 := by
    have heq : (⟨u * u, hmem⟩ : ↥Y) = ⟨u, huY⟩ * ⟨u, huY⟩ := by
      ext
      simp
    rw [heq, map_mul, hKexp (φ ⟨u, huY⟩) huK]
  have hone : (⟨u * u, hmem⟩ : ↥Y) = ⟨1, Y.one_mem⟩ :=
    φ.injective (hφ.trans (map_one φ).symm)
  exact congrArg (fun x : ↥Y => (x : G)) hone

private theorem caNormU_mem_liftSub_of_commute (hS : CentASetting m Y L R b t φ)
    {K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))}
    (hKcent : ∀ u ∈ uSub 1 m, (∀ v ∈ K, u * v = v * u) → u ∈ K)
    {u : G} (hu : u ∈ liftSub φ (uSub 1 m))
    (hc : ∀ v ∈ liftSub φ K, u * v = v * u) :
    u ∈ liftSub φ K := by
  obtain ⟨huY, huU⟩ := (mem_liftSub (K := uSub 1 m)).mp hu
  have hcomm : ∀ v : ↥K,
      φ ⟨u, huY⟩ * (v : GL (BlkIdx 1 m) (ZMod 2)) =
        (v : GL (BlkIdx 1 m) (ZMod 2)) * φ ⟨u, huY⟩ := by
    intro v
    let vY : ↥Y := φ.symm v
    have hvmem : ((vY : ↥Y) : G) ∈ liftSub φ K := by
      refine (mem_liftSub (K := K)).mpr ⟨vY.2, ?_⟩
      show φ vY ∈ K
      rw [show φ vY = v from φ.apply_symm_apply v]
      exact v.2
    have h := hc ((vY : ↥Y) : G) hvmem
    have h_mul : (⟨u, huY⟩ : ↥Y) * vY = vY * ⟨u, huY⟩ := by
      apply Subtype.ext
      simpa [Subgroup.coe_mul] using h
    have hthis := congrArg (fun x : ↥Y => φ x) h_mul
    rw [map_mul, map_mul] at hthis
    have hφv : φ vY = v := φ.apply_symm_apply v
    rw [hφv] at hthis
    exact hthis
  exact (mem_liftSub (K := K)).mpr
    ⟨huY, hKcent (φ ⟨u, huY⟩) huU fun v hv => hcomm ⟨v, hv⟩⟩

private theorem caNormU_isPGroup_liftSub_uSub (hS : CentASetting m Y L R b t φ) :
    IsPGroup 2 (liftSub φ (uSub 1 m)) := by
  have hcard : Nat.card (liftSub φ (uSub 1 m)) = 2 ^ (1 * 1 + 2 * 1 * m) := by
    change Nat.card (Subgroup.map Y.subtype
      (Subgroup.map φ.symm.toMonoidHom (uSub 1 m))) = _
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y)]
    rw [Subgroup.card_map_of_injective (φ.symm.injective)]
    exact card_uSub 1 m
  exact IsPGroup.of_card (n := 1 * 1 + 2 * 1 * m) hcard

private theorem caNormU_centralizer_le_uSub (hchar : IsCharTwoType G)
    (hS : CentASetting m Y L R b t φ) (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2)))
    (hJ : jGL 1 m ∈ K)
    (hKn : ∀ g ∈ Cent 1 m, ∀ u ∈ K, g * u * g⁻¹ ∈ K)
    (hKexp : ∀ u ∈ K, u * u = 1)
    (hKcent : ∀ u ∈ uSub 1 m, (∀ v ∈ K, u * v = v * u) → u ∈ K) :
    Subgroup.centralizer (liftSub φ K : Set G) ≤ liftSub φ (uSub 1 m) := by
  let U₁ : Subgroup G := liftSub φ K
  let U : Subgroup G := liftSub φ (uSub 1 m)
  let C : Subgroup G := Subgroup.centralizer (U₁ : Set G)
  have htU₁ : t ∈ U₁ := caNormU_t_mem_liftSub hS hJ
  have hCH : C ≤ Subgroup.centralizer ({t} : Set G) := by
    intro c hc
    have hct : c * t = t * c := by
      have := Subgroup.mem_centralizer_iff.mp hc t htU₁
      exact this.symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr hct
  have hU2 : IsPGroup 2 U := caNormU_isPGroup_liftSub_uSub hS
  have hcomm : ∀ (c : G) (hc : c ∈ C) (u : G) (hu : u ∈ U),
      c * u * c⁻¹ * u⁻¹ ∈ U₁ := by
    intro c hc u hu
    have hc_cent : ∀ v ∈ U₁, c * v = v * c := by
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp hc v hv).symm
    have hcH : c ∈ Subgroup.centralizer ({t} : Set G) := hCH hc
    have hcu : c * u * c⁻¹ ∈ U := conj_mem_liftSub_uSub hchar hS hcH hu
    have hwU : c * u * c⁻¹ * u⁻¹ ∈ U := U.mul_mem hcu (U.inv_mem hu)
    have hu_cent : u ∈ liftSub φ (Cent 1 m) := liftSub_mono (uSub_le_cent 1 m) hu
    have huinv_cent : u⁻¹ ∈ liftSub φ (Cent 1 m) := (liftSub φ (Cent 1 m)).inv_mem hu_cent
    have hw_cent : ∀ v ∈ U₁, (c * u * c⁻¹ * u⁻¹) * v = v * (c * u * c⁻¹ * u⁻¹) := by
      intro v hv
      have hnv : u⁻¹ * v * u ∈ U₁ := by
        simpa using caNormU_conj_mem_liftSub hS hKn huinv_cent hv
      have hcv : c * (u⁻¹ * v * u) = (u⁻¹ * v * u) * c := hc_cent (u⁻¹ * v * u) hnv
      have hcv' : c⁻¹ * (u⁻¹ * v * u) * c = u⁻¹ * v * u := by
        calc
          c⁻¹ * (u⁻¹ * v * u) * c = c⁻¹ * ((u⁻¹ * v * u) * c) := by group
          _ = c⁻¹ * (c * (u⁻¹ * v * u)) := by rw [← hcv]
          _ = u⁻¹ * v * u := by group
      have hinv : (c * u * c⁻¹ * u⁻¹) * v * (c * u * c⁻¹ * u⁻¹)⁻¹ = v := by
        calc
          (c * u * c⁻¹ * u⁻¹) * v * (c * u * c⁻¹ * u⁻¹)⁻¹ =
              c * u * (c⁻¹ * (u⁻¹ * v * u) * c) * u⁻¹ * c⁻¹ := by group
          _ = c * u * (u⁻¹ * v * u) * u⁻¹ * c⁻¹ := by rw [hcv']
          _ = c * (u * (u⁻¹ * v * u) * u⁻¹) * c⁻¹ := by group
          _ = c * v * c⁻¹ := by group
          _ = v := by
            have hvc : v * c = c * v := Subgroup.mem_centralizer_iff.mp hc v hv
            calc
              c * v * c⁻¹ = v * c * c⁻¹ := by rw [← hvc]
              _ = v := by group
      have hW := congrArg (fun x => x * (c * u * c⁻¹ * u⁻¹)) hinv
      simpa [mul_assoc] using hW
    exact caNormU_mem_liftSub_of_commute hS hKcent hwU hw_cent
  have hc2U : ∀ c : C, ((c : G) ^ 2) ∈ U := by
    intro c
    refine mem_liftSub_uSub_of_commutator hchar hS ?_ ?_
    · have hc2C : (c : G) ^ 2 ∈ C := C.pow_mem c.2 2
      exact hCH hc2C
    · intro u hu
      have hw : (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ U₁ := hcomm (c : G) c.2 u hu
      have hXc : ((c : G) * u * (c : G)⁻¹ * u⁻¹) * (c : G) =
          (c : G) * ((c : G) * u * (c : G)⁻¹ * u⁻¹) :=
        Subgroup.mem_centralizer_iff.mp c.2 ((c : G) * u * (c : G)⁻¹ * u⁻¹) hw
      have hcw : (c : G) * ((c : G) * u * (c : G)⁻¹ * u⁻¹) * (c : G)⁻¹ =
          (c : G) * u * (c : G)⁻¹ * u⁻¹ := by
        calc
          (c : G) * ((c : G) * u * (c : G)⁻¹ * u⁻¹) * (c : G)⁻¹ =
              ((c : G) * u * (c : G)⁻¹ * u⁻¹) * (c : G) * (c : G)⁻¹ := by
            rw [← hXc]
          _ = (c : G) * u * (c : G)⁻¹ * u⁻¹ := by group
      have hwu : (c : G) * u * (c : G)⁻¹ = ((c : G) * u * (c : G)⁻¹ * u⁻¹) * u := by
        group
      let w : G := (c : G) * u * (c : G)⁻¹ * u⁻¹
      have hwU₁ : w ∈ U₁ := hw
      have hw_c : (c : G) * w * (c : G)⁻¹ = w := hcw
      have hwu' : (c : G) * u * (c : G)⁻¹ = w * u := hwu
      have hcentral : (c : G) ^ 2 * u * ((c : G) ^ 2)⁻¹ = u := by
        calc
          (c : G) ^ 2 * u * ((c : G) ^ 2)⁻¹ =
              (c : G) * ((c : G) * u * (c : G)⁻¹) * (c : G)⁻¹ := by
            rw [pow_two, mul_inv_rev]
            group
          _ = (c : G) * (w * u) * (c : G)⁻¹ := by rw [hwu']
          _ = ((c : G) * w * (c : G)⁻¹) * ((c : G) * u * (c : G)⁻¹) := by group
          _ = w * (w * u) := by rw [hw_c, hwu']
          _ = (w * w) * u := by group
          _ = u := by
            rw [caNormU_mul_self_eq_one_of_mem_liftSub hS hKexp hwU₁]
            group
      have hone : (c : G) ^ 2 * u * ((c : G) ^ 2)⁻¹ * u⁻¹ = 1 := by
        rw [hcentral]
        group
      rw [hone]
      exact (Subgroup.zpowers t).one_mem
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨n, hn⟩ := hU2 ⟨(c : G) ^ 2, hc2U c⟩
    refine ⟨n + 1, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    have hnG : (((⟨(c : G) ^ 2, hc2U c⟩ : U) ^ 2 ^ n : U) : G) = 1 := by
      simpa using congrArg (fun x : U => (x : G)) hn
    rw [Subgroup.coe_pow] at hnG
    have h2 : 2 * 2 ^ n = 2 ^ (n + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [← pow_mul, h2] at hnG
    exact hnG
  have hCn : ∀ y ∈ liftSub φ (Cent 1 m), ∀ x ∈ C, y * x * y⁻¹ ∈ C := by
    intro y hy x hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro v hv
    have hyinv : y⁻¹ ∈ liftSub φ (Cent 1 m) := (liftSub φ (Cent 1 m)).inv_mem hy
    have hnv : y⁻¹ * v * y ∈ U₁ := by
      simpa using caNormU_conj_mem_liftSub hS hKn hyinv hv
    have hxv : x * (y⁻¹ * v * y) = (y⁻¹ * v * y) * x := by
      exact (Subgroup.mem_centralizer_iff.mp hx (y⁻¹ * v * y) hnv).symm
    calc
      v * (y * x * y⁻¹) = y * (y⁻¹ * v * y) * x * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * v * y)) * y⁻¹ := by
        rw [show y * (y⁻¹ * v * y) * x * y⁻¹ =
          y * ((y⁻¹ * v * y) * x) * y⁻¹ from by group]
        rw [← hxv]
      _ = (y * x * y⁻¹) * v := by group
  have hCU : C ≤ U := le_liftSub_uSub_of_invariant hS hC2 hCH hCn
  simpa [C, U, U₁] using hCU

private theorem caNormU_normalizer_le (hchar : IsCharTwoType G)
    (hS : CentASetting m Y L R b t φ) (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2)))
    (hJ : jGL 1 m ∈ K) (hKsub : K ≤ uSub 1 m)
    (hKn : ∀ g ∈ Cent 1 m, ∀ u ∈ K, g * u * g⁻¹ ∈ K)
    (hKexp : ∀ u ∈ K, u * u = 1)
    (hKcent : ∀ u ∈ uSub 1 m, (∀ v ∈ K, u * v = v * u) → u ∈ K)
    (hKaut : ∀ f : ↥K ≃* ↥K, ∃ y ∈ Subgroup.normalizer (K : Set (GL (BlkIdx 1 m) (ZMod 2))),
      ∀ u : ↥K, ((f u : ↥K) : GL (BlkIdx 1 m) (ZMod 2)) =
        y * (u : GL (BlkIdx 1 m) (ZMod 2)) * y⁻¹) :
    Subgroup.normalizer (liftSub φ K : Set G) ≤ Y := by
  intro h hh
  let U₁ : Subgroup G := liftSub φ K
  let U : Subgroup G := liftSub φ (uSub 1 m)
  have hCU : Subgroup.centralizer (U₁ : Set G) ≤ U :=
    caNormU_centralizer_le_uSub hchar hS K hJ hKn hKexp hKcent
  have hmap : Subgroup.map (↑(MulAut.conj h)) U₁ = U₁ := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hh y).mp hy
    · intro hx
      refine ⟨h⁻¹ * x * h, ?_, ?_⟩
      · have hhinv : h⁻¹ ∈ Subgroup.normalizer (U₁ : Set G) :=
          (Subgroup.normalizer (U₁ : Set G)).inv_mem hh
        simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hhinv x).mp hx
      · change h * (h⁻¹ * x * h) * h⁻¹ = x
        group
  let f₀ : ↥U₁ ≃* ↥U₁ :=
    ((MulAut.conj h).subgroupMap U₁).trans (MulEquiv.subgroupCongr hmap)
  let φ₁ : ↥U₁ ≃* ↥K :=
    { toFun := fun u =>
        (⟨φ ⟨(u : G), liftSub_le K u.2⟩, by
          obtain ⟨_, hu'⟩ := (mem_liftSub (K := K)).mp u.2
          exact hu'⟩ : ↥K)
      invFun := fun v =>
        (⟨((φ.symm v : ↥Y) : G), by
          refine (mem_liftSub (K := K)).mpr ⟨(φ.symm v).2, ?_⟩
          show φ ⟨((φ.symm v : ↥Y) : G), (φ.symm v).2⟩ ∈ K
          rw [show (⟨((φ.symm v : ↥Y) : G), (φ.symm v).2⟩ : ↥Y) = φ.symm v from rfl]
          rw [φ.apply_symm_apply]
          exact v.2⟩ : ↥U₁)
      left_inv := fun u => by
        apply Subtype.ext
        simp
      right_inv := fun v => by
        apply Subtype.ext
        simp
      map_mul' := fun u v => by
        apply Subtype.ext
        show φ ⟨((u * v : ↥U₁) : G),
          liftSub_le K (u * v).2⟩ =
          φ ⟨(u : G), liftSub_le K u.2⟩ *
            φ ⟨(v : G), liftSub_le K v.2⟩
        rw [show (⟨((u * v : ↥U₁) : G),
            liftSub_le K (u * v).2⟩ : ↥Y) =
          ⟨(u : G), liftSub_le K u.2⟩ *
            ⟨(v : G), liftSub_le K v.2⟩ from by
          ext
          rfl]
        rw [map_mul] }
  let f : ↥K ≃* ↥K := φ₁.symm.trans (f₀.trans φ₁)
  obtain ⟨y₀, _, hconj⟩ := hKaut f
  let y : G := ((φ.symm y₀ : ↥Y) : G)
  have hyY : y ∈ Y := (φ.symm y₀).2
  have hf₀_coe : ∀ u : ↥U₁, ((f₀ u : ↥U₁) : G) = h * (u : G) * h⁻¹ := by
    intro u
    change (((MulEquiv.subgroupCongr hmap) ((MulAut.conj h).subgroupMap U₁ u) : ↥U₁) : G) = _
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have hu_coe : ∀ u : ↥U₁, ((φ.symm (φ₁ u) : ↥Y) : G) = (u : G) := by
    intro u
    have heq : (φ.symm (φ₁ u) : ↥Y) =
        ⟨(u : G), liftSub_le K u.2⟩ := by
      apply φ.injective
      rw [φ.apply_symm_apply]
      rfl
    exact congrArg (fun z : ↥Y => (z : G)) heq
  have hconj_u : ∀ u : ↥U₁, h * (u : G) * h⁻¹ = y * (u : G) * y⁻¹ := by
    intro u
    have hf_eq : (↑(f (φ₁ u)) : GL (BlkIdx 1 m) (ZMod 2)) = ↑(φ₁ (f₀ u)) := by
      change (↑((φ₁.symm.trans (f₀.trans φ₁)) (φ₁ u)) : GL (BlkIdx 1 m) (ZMod 2)) = _
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
    have hf' : (↑(φ₁ (f₀ u)) : GL (BlkIdx 1 m) (ZMod 2)) =
        y₀ * ↑(φ₁ u) * y₀⁻¹ := by
      rw [← hf_eq]
      exact hconj (φ₁ u)
    have hL : (φ.symm (↑(φ₁ (f₀ u)) : GL (BlkIdx 1 m) (ZMod 2)) : ↥Y) =
        ⟨(f₀ u : G), liftSub_le K (f₀ u).2⟩ := by
      apply φ.injective
      rw [φ.apply_symm_apply]
      rfl
    have hφ := congrArg (fun z : GL (BlkIdx 1 m) (ZMod 2) => φ.symm z) hf'
    rw [hL] at hφ
    simp only [map_mul, map_inv] at hφ
    have hco := congrArg (fun z : ↥Y => (z : G)) hφ
    rw [hf₀_coe u] at hco
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hco
    rw [hu_coe u] at hco
    simpa [y] using hco
  have hyh : y⁻¹ * h ∈ Subgroup.centralizer (U₁ : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro u hu
    have hconj_u' := hconj_u ⟨u, hu⟩
    have h1 : (y⁻¹ * h) * u * (y⁻¹ * h)⁻¹ = u := by
      calc
        (y⁻¹ * h) * u * (y⁻¹ * h)⁻¹ = y⁻¹ * (h * u * h⁻¹) * y := by group
        _ = y⁻¹ * (y * u * y⁻¹) * y := by rw [hconj_u']
        _ = u := by group
    calc
      u * (y⁻¹ * h) = ((y⁻¹ * h) * u * (y⁻¹ * h)⁻¹) * (y⁻¹ * h) := by rw [h1]
      _ = (y⁻¹ * h) * u := by group
  have hyhY : y⁻¹ * h ∈ Y := by
    have := hCU hyh
    exact liftSub_le (uSub 1 m) this
  have heq : h = y * (y⁻¹ * h) := by group
  rw [heq]
  exact Y.mul_mem hyY hyhY

theorem normalizer_liftSub_uOne_le (hchar : IsCharTwoType G) (hS : CentASetting m Y L R b t φ) :
    Subgroup.normalizer (liftSub φ (uOne m) : Set G) ≤ Y := by
  exact caNormU_normalizer_le hchar hS (uOne m) (jGL_mem_uOne m) (uOne_le_uSub m)
    (fun g hg u hu => conj_mem_uOne hg hu)
    (fun u hu => mul_self_eq_one_of_mem_uOne hu)
    (fun u hu hc => mem_uOne_of_commute hu hc)
    (fun f => exists_normalizer_uOne_of_mulEquiv f)

theorem normalizer_liftSub_uTwo_le (hchar : IsCharTwoType G) (hS : CentASetting m Y L R b t φ) :
    Subgroup.normalizer (liftSub φ (uTwo m) : Set G) ≤ Y := by
  exact caNormU_normalizer_le hchar hS (uTwo m) (jGL_mem_uTwo m) (uTwo_le_uSub m)
    (fun g hg u hu => conj_mem_uTwo hg hu)
    (fun u hu => mul_self_eq_one_of_mem_uTwo hu)
    (fun u hu hc => mem_uTwo_of_commute hu hc)
    (fun f => exists_normalizer_uTwo_of_mulEquiv f)

end CFSG.StandardType.FF81.CentA

end
