module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUC

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

private theorem qtwoDB44_s5_conj_injective {H : Type} [Group H]
    (hZ : Subgroup.center H = ⊥) :
    Function.Injective (MulAut.conj : H →* MulAut H) := by
  intro u v huv
  have hc : v⁻¹ * u ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro n
    have h1 := congrArg (fun φ : MulAut H => φ n) huv
    simp only [MulAut.conj_apply] at h1
    calc n * (v⁻¹ * u) = v⁻¹ * (v * n * v⁻¹) * u := by group
      _ = v⁻¹ * (u * n * u⁻¹) * u := by rw [← h1]
      _ = (v⁻¹ * u) * n := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem qtwoDB44_torus_of {N : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    (hZ : Subgroup.center ↥N = ⊥)
    (hker_char : ∀ s : ↥Bs, ggGamma N hBsN s = 1 ↔
      ∀ k : Fin m, k ≠ c → βL (Additive.ofMul s) k = 0)
    (hInner : (ggGamma N hBsN).range ≤ (MulAut.conj : ↥N →* MulAut ↥N).range)
    (hSelf : GGTorusSelfCent 3 (ggGamma N hBsN).range)
    {Θ : ↥(dEvenStab m (Pi.single c 1)) →*
      ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range (ggGamma N hBsN).range)}
    (hΘact : ∀ (w : ↥(dEvenStab m (Pi.single c 1))) (s : ↥Bs),
      (Θ w : MulAut ↥(ggGamma N hBsN).range) ((ggGamma N hBsN).rangeRestrict s) =
        (ggGamma N hBsN).rangeRestrict (Additive.toMul (βL.symm
          ((w : DVec m ≃ₗ[ZMod 3] DVec m) (βL (Additive.ofMul s)))))) :
    ∃ τ : Multiplicative (DVec m) →* ↥N,
      (∀ v : DVec m, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0) ∧
      (∀ (s : ↥Bs) (n : ↥N), ggGamma N hBsN s n =
        τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) * n *
          (τ (Multiplicative.ofAdd (βL (Additive.ofMul s))))⁻¹) ∧
      (∀ z : ↥N, (∀ v : DVec m, z * τ (Multiplicative.ofAdd v) = τ (Multiplicative.ofAdd v) * z) →
        z ^ 3 = 1 → z ∈ τ.range) ∧
      (∀ w ∈ dEvenStab m (Pi.single c 1), ∃ y : ↥N, ∀ v : DVec m,
        y * τ (Multiplicative.ofAdd v) * y⁻¹ = τ (Multiplicative.ofAdd (w v))) ∧
      (∀ (s : ↥Bs) (n : ↥N), (s : G) * n = n * s →
        n * τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) =
          τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) * n) := by
  classical
  have hconj_inj : Function.Injective (MulAut.conj : ↥N →* MulAut ↥N) :=
    qtwoDB44_s5_conj_injective hZ
  let inn : ↥N ≃* (MulAut.conj : ↥N →* MulAut ↥N).range :=
    MonoidHom.ofInjective hconj_inj
  let σ : ↥Bs →* ↥N :=
    inn.symm.toMonoidHom.comp
      ((ggGamma N hBsN).codRestrict _ fun s => hInner ⟨s, rfl⟩)
  have hσ_spec : ∀ s : ↥Bs, MulAut.conj (σ s) = ggGamma N hBsN s := by
    intro s
    have h := MonoidHom.apply_ofInjective_symm hconj_inj
      (⟨ggGamma N hBsN s, hInner ⟨s, rfl⟩⟩ :
        (MulAut.conj : ↥N →* MulAut ↥N).range)
    exact h
  let βLhom : Multiplicative (DVec m) →* ↥Bs :=
    { toFun := fun v => Additive.toMul (βL.symm (Multiplicative.toAdd v))
      map_one' := by
        change Additive.toMul (βL.symm 0) = (1 : ↥Bs)
        rw [map_zero]
        rfl
      map_mul' := fun v w => by
        apply Additive.ofMul.injective
        change βL.symm (Multiplicative.toAdd v + Multiplicative.toAdd w) =
          βL.symm (Multiplicative.toAdd v) + βL.symm (Multiplicative.toAdd w)
        rw [map_add] }
  let τ : Multiplicative (DVec m) →* ↥N := σ.comp βLhom
  have hτ_ofAdd : ∀ v : DVec m,
      τ (Multiplicative.ofAdd v) = σ (Additive.toMul (βL.symm v)) := fun _ => rfl
  have hτ_beta : ∀ s : ↥Bs,
      τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) = σ s := by
    intro s
    rw [hτ_ofAdd]
    congr 1
    rw [AddEquiv.symm_apply_apply]
    exact ofMul_toMul s
  refine ⟨τ, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    have hτv : τ (Multiplicative.ofAdd v) = σ (Additive.toMul (βL.symm v)) := hτ_ofAdd v
    constructor
    · intro h i hi
      have h1 : ggGamma N hBsN (Additive.toMul (βL.symm v)) = 1 := by
        rw [← hσ_spec (Additive.toMul (βL.symm v)), ← hτv, h, map_one]
      simpa using (hker_char _).mp h1 i hi
    · intro hv
      have h1 : ggGamma N hBsN (Additive.toMul (βL.symm v)) = 1 :=
        (hker_char _).mpr (by simpa using hv)
      apply hconj_inj
      rw [hτv, hσ_spec (Additive.toMul (βL.symm v)), h1, map_one]
  · intro s n
    rw [← hσ_spec s, hτ_beta s, MulAut.conj_apply]
  · intro z hz hz3
    have hz' : ∀ a ∈ (ggGamma N hBsN).range, a z = z := by
      intro a ha
      obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp ha
      rw [← hσ_spec s, MulAut.conj_apply]
      have hcomm : z * τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) =
          τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) * z := hz _
      rw [hτ_beta s] at hcomm
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm.symm
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (hSelf z hz' hz3)
    refine MonoidHom.mem_range.mpr
      ⟨Multiplicative.ofAdd (βL (Additive.ofMul s)), ?_⟩
    rw [hτ_beta s]
    apply hconj_inj
    rw [hσ_spec s, hs]
  · intro w hw
    let w' : ↥(dEvenStab m (Pi.single c 1)) := ⟨w, hw⟩
    obtain ⟨g, hgH, -, hgact⟩ := mem_ggAutomizer_iff.mp (Θ w').2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hgH
    refine ⟨y, ?_⟩
    intro v
    let s : ↥Bs := Additive.toMul (βL.symm v)
    let t : ↥Bs := Additive.toMul (βL.symm (w v))
    have hsβ : βL (Additive.ofMul s) = v := by
      change βL (βL.symm v) = v
      exact AddEquiv.apply_symm_apply βL v
    have h1val := congrArg (fun z : ↥(ggGamma N hBsN).range => (z : MulAut ↥N))
      (hΘact w' s)
    have h2val := hgact ((ggGamma N hBsN).rangeRestrict s)
    simp only [MonoidHom.coe_rangeRestrict] at h1val h2val
    have h1 : ((Θ w' : MulAut ↥(ggGamma N hBsN).range)
          ((ggGamma N hBsN).rangeRestrict s) : MulAut ↥N) = ggGamma N hBsN t := by
      rw [h1val, hsβ]
    have hgg : ggGamma N hBsN t = g * ggGamma N hBsN s * g⁻¹ := by
      rw [← h1]
      exact h2val
    have hconj : MulAut.conj (σ t) =
        MulAut.conj y * MulAut.conj (σ s) * (MulAut.conj y)⁻¹ := by
      rw [hσ_spec t, hgg, hy, ← hσ_spec s]
    have hprod : MulAut.conj y * MulAut.conj (σ s) * (MulAut.conj y)⁻¹ =
        MulAut.conj (y * σ s * y⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    have hconj' : σ t = y * σ s * y⁻¹ := hconj_inj (hconj.trans hprod)
    have hτv : σ s = τ (Multiplicative.ofAdd v) := (hτ_ofAdd v).symm
    have hτw : σ t = τ (Multiplicative.ofAdd (w v)) := (hτ_ofAdd (w v)).symm
    rw [← hτv, ← hτw]
    exact hconj'.symm
  · intro s n hsn
    have hγ : ggGamma N hBsN s n = n := by
      apply Subtype.ext
      rw [ggGamma_coe]
      change (s : G) * (n : G) * (s : G)⁻¹ = (n : G)
      rw [hsn]
      group
    have h2 : τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) * n *
        (τ (Multiplicative.ofAdd (βL (Additive.ofMul s))))⁻¹ = n := by
      rw [hτ_beta s, ← MulAut.conj_apply, hσ_spec s]
      exact hγ
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm


theorem qtwoDB44_torus (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    {N : Subgroup G} (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    (hBsN : Bs ≤ Subgroup.normalizer (N : Set G)) (hZ : Subgroup.center ↥N = ⊥) :
    ∃ τ : Multiplicative (DVec m) →* ↥N,
      (∀ v : DVec m, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0) ∧
      (∀ (s : ↥Bs) (n : ↥N), ggGamma N hBsN s n =
        τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) * n *
          (τ (Multiplicative.ofAdd (βL (Additive.ofMul s))))⁻¹) ∧
      (∀ z : ↥N, (∀ v : DVec m, z * τ (Multiplicative.ofAdd v) = τ (Multiplicative.ofAdd v) * z) →
        z ^ 3 = 1 → z ∈ τ.range) ∧
      (∀ w ∈ dEvenStab m (Pi.single c 1), ∃ y : ↥N, ∀ v : DVec m,
        y * τ (Multiplicative.ofAdd v) * y⁻¹ = τ (Multiplicative.ofAdd (w v))) ∧
      (∀ n : ↥N, (n : G) ∈ qtwoDelJ ψ c →
        n * τ (Multiplicative.ofAdd (fun _ => 1)) = τ (Multiplicative.ofAdd (fun _ => 1)) * n) ∧
      (∀ n : ↥N, (n : G) ∈ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom →
        n * τ (Multiplicative.ofAdd (dSign m a b (fun _ => 1))) =
          τ (Multiplicative.ofAdd (dSign m a b (fun _ => 1))) * n) := by
  classical
  obtain ⟨hker_char, -, -, hInner, hSelf⟩ :=
    qtwoDB36_gamma (by omega) hbase hcoords hdel hN hJ₁ hJ₂ hBsN
  obtain ⟨Θ, -, hΘact⟩ :=
    qtwoDB36_weyl_embed (by omega) hbase hcoords hdel hN hJ₁ hJ₂ hBsN
  obtain ⟨τ, hτker, hconj, hsc, hW, hcomm⟩ :=
    qtwoDB44_torus_of hBsN hZ hker_char hInner hSelf hΘact
  have hJ₁leL : qtwoDelJ ψ c ≤ L := by
    change (CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary.coordBlockSU F0 2 1
      (Finset.univ.erase c)).map ψ ≤ L
    rw [← hbase.range]
    exact Subgroup.map_le_range _ _
  have hxCentL : x ∈ Subgroup.centralizer (L : Set G) := by
    have hmem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hbase.cent]
      exact Subgroup.mem_zpowers x
    exact hmem.2
  refine ⟨τ, hτker, hconj, hsc, hW, ?_, ?_⟩
  · intro n hn
    have hxcomm : x * (n : G) = (n : G) * x :=
      ((Subgroup.mem_centralizer_iff.mp hxCentL) (n : G) (hJ₁leL hn)).symm
    have h := hcomm ⟨x, hbase.x_mem⟩ n hxcomm
    rwa [hcoords.x_coord hbase.x_mem] at h
  · intro n hn
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_map.mp hn
    have hxcomm : x * (j : G) = (j : G) * x :=
      ((Subgroup.mem_centralizer_iff.mp hxCentL) (j : G) (hJ₁leL hj)).symm
    have hn_eq : (n : G) = g * (j : G) * g⁻¹ := by
      rw [← hjn]
      rfl
    have hαcomm : ((α ⟨x, hbase.x_mem⟩ : ↥Bs) : G) * n =
        n * ((α ⟨x, hbase.x_mem⟩ : ↥Bs) : G) := by
      rw [hdel.conj ⟨x, hbase.x_mem⟩, hn_eq]
      calc g * x * g⁻¹ * (g * (j : G) * g⁻¹) = g * (x * (j : G)) * g⁻¹ := by group
        _ = g * ((j : G) * x) * g⁻¹ := by rw [hxcomm]
        _ = g * (j : G) * g⁻¹ * (g * x * g⁻¹) := by group
    have h := hcomm (α ⟨x, hbase.x_mem⟩) n hαcomm
    have hαβ : βL (Additive.ofMul (α ⟨x, hbase.x_mem⟩)) = dSign m a b (fun _ => 1) := by
      rw [hdel.sign ⟨x, hbase.x_mem⟩, hcoords.x_coord hbase.x_mem]
    rwa [hαβ] at h

end CFSG.StandardType.QTwo

end
