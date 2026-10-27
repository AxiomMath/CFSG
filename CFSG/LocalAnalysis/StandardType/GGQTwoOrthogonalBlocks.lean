module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCentralizer
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Chamber

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {n : ℕ} {B Bs L D J : Subgroup G} {x : G}

theorem ggCentralizer_coordZeroOn_le_normalizer_of_component {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBsEA : IsElemAbelian p Bs)
    (hxBs : x ∈ Bs) (hx1 : x ≠ 1)
    (hComp : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n p i0)
    {S : Set (Fin n)} (hi0 : i0 ∉ S)
    (houtside : ∃ j : Fin n, j ≠ i0 ∧ j ∉ S) :
    Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro g hg
  have hLx := hComp.1
  have hxcoord : ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1 :=
    ggBs_coord_eq_one_of_mem_bCoordinateBlock hp hp2 hxBs hLx eta i0 hLeta
  have hxH : x ∈ ggBsCoordZeroOn Bs eta S := by
    rw [mem_ggBsCoordZeroOn]
    refine ⟨hxBs, fun j hj => hxcoord j (fun hji => hi0 (hji ▸ hj))⟩
  obtain ⟨j, hji0, hjS⟩ := houtside
  let v : Fin n → Multiplicative (ZMod p) :=
    Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))
  let b : ↥Bs := eta.symm v
  have hbcoord : eta b i0 = 1 := by
    have hb : eta b = v := by simp [b]
    rw [hb]
    exact Pi.mulSingle_eq_of_ne (Ne.symm hji0) _
  have hbL : (b : G) ∈ L :=
    (ggBs_mem_iff_coord_eq_one_of_bCoordinateBlock hp hp2 hBsEA hxBs hx1 hLx
      hZ hN eta i0 hLeta b).mpr hbcoord
  have hbH : (b : G) ∈ ggBsCoordZeroOn Bs eta S := by
    rw [mem_ggBsCoordZeroOn]
    refine ⟨b.2, fun j' hj' => ?_⟩
    have hb : eta b = v := by simp [b]
    have hne : j' ≠ j := fun h => hjS (h ▸ hj')
    rw [show eta ⟨(b : G), b.2⟩ = eta b from rfl, hb]
    exact Pi.mulSingle_eq_of_ne hne _
  have hb_ne_one : (b : G) ≠ 1 := by
    intro hb1
    have hb_eq_one : b = 1 := Subtype.ext hb1
    have hv_eq_one : v = 1 := by
      rw [← show eta b = v by simp [b], hb_eq_one]
      exact map_one eta
    have h10 : (1 : ZMod p) = 0 := by
      have h := congrArg toAdd (congrFun hv_eq_one j)
      simpa [v] using h
    exact one_ne_zero h10
  have hbnc : (b : G) ∉ Subgroup.centralizer (L : Set G) := by
    intro hbC
    have hbcenter : (⟨b, hbL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hbC (l : G) l.2)
    rw [hZ] at hbcenter
    have hb1 : (b : G) = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hbcenter)
    exact hb_ne_one hb1
  have hgx : g * x = x * g :=
    (Subgroup.mem_centralizer_iff.mp hg x hxH).symm
  have hgH : g ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hgx)
  have hgb : g * (b : G) = (b : G) * g :=
    (Subgroup.mem_centralizer_iff.mp hg (b : G) hbH).symm
  exact ggMem_normalizer_of_component hComp hbL hbnc hgH hgb

theorem ggCentralizer_coordZeroOn_le_normalizer_of_bCoordinateBlock
    (hcfg : GGConfig 3 B Bs x L D J) (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (i0 : Fin n)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {S : Set (Fin n)} (hi0 : i0 ∉ S)
    (houtside : ∃ j : Fin n, j ≠ i0 ∧ j ∉ S) :
    Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  obtain ⟨hp, hBsEA, hxBs, -, -⟩ := hcfg.tableB_facts
  exact ggCentralizer_coordZeroOn_le_normalizer_of_component hp (by decide) hBsEA hxBs
    hcfg.1.2.2.2.2.2.2.1.2.2.1 hcfg.1.2.2.2.2.2.2.1.2.2.2.1 hZ hN eta i0 hLeta hi0 houtside

section OrthogonalNeighbourFrameTransport

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
  {p n r f : ℕ} {E : QuadExt F K (unitaryInvolution K 2 f)}

theorem GGSecFiveBPermOmKFrame.conj_eq_normPlaneTorus
    {G : Type} [Group G] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 1) ≃ Fin n} {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hr : 2 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) :
    ∀ (b : ↥Bs) (s : normOmega E r),
      (b : G) * κ s * (b : G)⁻¹ =
        κ (normPlaneTorus E hr hpq χ (fun i => eta b (π i.castSucc)) * s *
          (normPlaneTorus E hr hpq χ (fun i => eta b (π i.castSucc)))⁻¹) := by
  intro b s
  obtain ⟨T, hTact, hTconj⟩ := hframe.2.2.2 b
  have hT : T = normPlaneTorus E hr hpq χ (fun i => eta b (π i.castSucc)) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hTact v, normPlaneTorus_apply E hr hpq χ (fun i => eta b (π i.castSucc)) v]
  rw [← hT]
  exact hTconj s

theorem GGSecFiveBPermOmKFrame.inf_centralizer_coordZeroOn_eq_map
    {G : Type} [Group G] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 1) ≃ Fin n} {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hr : 2 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (S : Finset (Fin r)) :
    X ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta
        ((fun i : Fin r => π i.castSucc) '' (S : Set (Fin r))) : Set G) =
      (Subgroup.centralizer (((Subgroup.pi (S : Set (Fin r))
        (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p))))).map
          (normPlaneTorus E hr hpq χ)) : Set (normOmega E r))).map κ := by
  classical
  let τ : (Fin r → Multiplicative (ZMod p)) →* normOmega E r := normPlaneTorus E hr hpq χ
  let A : Subgroup (Fin r → Multiplicative (ZMod p)) :=
    Subgroup.pi (S : Set (Fin r)) (fun _ => ⊥)
  let H : Subgroup G := ggBsCoordZeroOn Bs eta
    ((fun i : Fin r => π i.castSucc) '' (S : Set (Fin r)))
  apply le_antisymm
  · intro g hg
    obtain ⟨hgX, hgC⟩ := hg
    have hgRange : g ∈ κ.range := by
      rw [hframe.2.1]
      exact hgX
    obtain ⟨t, rfl⟩ := hgRange
    refine Subgroup.mem_map_of_mem κ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    change a ∈ A.map τ at ha
    obtain ⟨u, huA, rfl⟩ := Subgroup.mem_map.mp ha
    let uFull : Fin n → Multiplicative (ZMod p) :=
      fun k => (π.symm k).lastCases 1 (fun i => u i)
    let b : ↥Bs := eta.symm uFull
    have hbcoord : (fun i : Fin r => eta b (π i.castSucc)) = u := by
      funext i
      have hb : eta b = uFull := by simp [b]
      rw [hb]
      simp [uFull, Fin.lastCases_castSucc]
    have hbH : (b : G) ∈ H := by
      rw [show H = ggBsCoordZeroOn Bs eta
        ((fun i : Fin r => π i.castSucc) '' (S : Set (Fin r))) from rfl, mem_ggBsCoordZeroOn]
      refine ⟨b.2, ?_⟩
      rintro j ⟨i, hi, rfl⟩
      have hbi := congrFun hbcoord i
      rw [hbi]
      exact Subgroup.mem_bot.mp ((Subgroup.mem_pi (S : Set (Fin r))).mp huA i hi)
    have hcomm : (b : G) * κ t = κ t * (b : G) :=
      (Subgroup.mem_centralizer_iff.mp hgC) (b : G) hbH
    have hconj := GGSecFiveBPermOmKFrame.conj_eq_normPlaneTorus
      (hr := hr) (hpq := hpq) (hframe := hframe) b t
    rw [hbcoord] at hconj
    have hleft : (b : G) * κ t * (b : G)⁻¹ = κ t := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hleft] at hconj
    have htu : τ u * t * (τ u)⁻¹ = t := hframe.1 hconj.symm
    calc τ u * t = (τ u * t * (τ u)⁻¹) * τ u := by group
      _ = t * τ u := by rw [htu]
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨?_, ?_⟩
    · rw [← hframe.2.1]
      exact ⟨t, rfl⟩
    · change κ t ∈ Subgroup.centralizer (H : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      change b ∈ ggBsCoordZeroOn Bs eta
        ((fun i : Fin r => π i.castSucc) '' (S : Set (Fin r))) at hb
      rw [mem_ggBsCoordZeroOn] at hb
      obtain ⟨hbBs, hbcoord⟩ := hb
      let u : Fin r → Multiplicative (ZMod p) := fun i => eta ⟨b, hbBs⟩ (π i.castSucc)
      have huA : u ∈ A := by
        rw [Subgroup.mem_pi]
        intro i hi
        rw [Subgroup.mem_bot]
        exact hbcoord (π i.castSucc) ⟨i, hi, rfl⟩
      have hcomm : τ u * t = t * τ u :=
        (Subgroup.mem_centralizer_iff.mp ht) (τ u) (Subgroup.mem_map_of_mem τ huA)
      have hconj := GGSecFiveBPermOmKFrame.conj_eq_normPlaneTorus
        (hr := hr) (hpq := hpq) (hframe := hframe) ⟨b, hbBs⟩ t
      have htu : τ u * t * (τ u)⁻¹ = t := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [htu] at hconj
      calc b * κ t = (b * κ t * b⁻¹) * b := by group
        _ = κ t * b := by rw [hconj]

theorem GGSecFiveBPermOmKFrame.normPlaneTorus_mem_Bs_of_dvd
    {G : Type} [Group G] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 1) ≃ Fin n} {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hr : 2 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (u : Fin r → Multiplicative (ZMod p)) :
    κ (normPlaneTorus E hr hpq χ u) ∈ Bs := by
  let τ : (Fin r → Multiplicative (ZMod p)) →* normOmega E r := normPlaneTorus E hr hpq χ
  let t : normOmega E r := τ u
  have htp : t ^ p = 1 := by
    have hup : u ^ p = 1 := by
      funext i
      apply toAdd.injective
      rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, ZMod.natCast_self,
        zero_mul]
    rw [show t = τ u from rfl, ← map_pow, hup, map_one]
  refine hSC (κ t) ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    let v : Fin r → Multiplicative (ZMod p) := fun i => eta ⟨b, hb⟩ (π i.castSucc)
    have hvcomm : τ v * t = t * τ v := by
      rw [show t = τ u from rfl, ← map_mul, ← map_mul, mul_comm]
    have hconj := GGSecFiveBPermOmKFrame.conj_eq_normPlaneTorus
      (hr := hr) (hpq := hpq) (hframe := hframe) ⟨b, hb⟩ t
    have hleft : b * κ t * b⁻¹ = κ t := by
      rw [hconj]
      congr 1
      rw [hvcomm, mul_assoc, mul_inv_cancel, mul_one]
    calc b * κ t = (b * κ t * b⁻¹) * b := by group
      _ = κ t * b := by rw [hleft]
  · rw [← map_pow, htp, map_one]

theorem GGSecFiveBPermOmKFrame.coords_normPlaneTorus_of_dvd
    {G : Type} [Group G] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 1) ≃ Fin n} {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hr : 2 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (u : Fin r → Multiplicative (ZMod p)) (i : Fin r) :
    eta ⟨κ (normPlaneTorus E hr hpq χ u),
        hframe.normPlaneTorus_mem_Bs_of_dvd hr hpq hSC u⟩ (π i.castSucc) = u i := by
  let τ : (Fin r → Multiplicative (ZMod p)) →* normOmega E r := normPlaneTorus E hr hpq χ
  let t : normOmega E r := τ u
  let b : ↥Bs := ⟨κ t, hframe.normPlaneTorus_mem_Bs_of_dvd hr hpq hSC u⟩
  let v : Fin r → Multiplicative (ZMod p) := fun i => eta b (π i.castSucc)
  have hv : v = u := by
    have hτv : τ v = τ u := by
      have hcentral : (τ v)⁻¹ * t ∈ Subgroup.center (normOmega E r) := by
        rw [Subgroup.mem_center_iff]
        intro s
        have hs : t * s * t⁻¹ = τ v * s * (τ v)⁻¹ := by
          have hconj := GGSecFiveBPermOmKFrame.conj_eq_normPlaneTorus
            (hr := hr) (hpq := hpq) (hframe := hframe) b s
          have hleft : (b : G) * κ s * (b : G)⁻¹ = κ (t * s * t⁻¹) := by
            change κ t * κ s * (κ t)⁻¹ = κ (t * s * t⁻¹)
            simp only [← map_mul, ← map_inv]
          rw [hleft] at hconj
          exact hframe.1 hconj
        have hzs : (τ v)⁻¹ * t * s = s * ((τ v)⁻¹ * t) := by
          calc (τ v)⁻¹ * t * s = (τ v)⁻¹ * (t * s * t⁻¹) * t := by group
            _ = (τ v)⁻¹ * (τ v * s * (τ v)⁻¹) * t := by rw [hs]
            _ = s * ((τ v)⁻¹ * t) := by group
        exact hzs.symm
      have hz1 : (τ v)⁻¹ * t = 1 := by
        have := hcentral
        rw [center_normOmega_eq_bot E hr] at this
        exact Subgroup.mem_bot.mp this
      have hτvt : τ v = t := inv_mul_eq_one.mp hz1
      exact hτvt.trans (show t = τ u from rfl)
    exact normPlaneTorus_injective E hr hpq hframe.2.2.1 hτv
  exact congrFun hv i

section ActivePlaneTorus

variable {E₁ : QuadExt F K (unitaryInvolution K 2 1)}

theorem GGSecFiveBPermOmKFrame.normPlaneTorus_mem_Bs
    {G : Type} [Group G] {Bs X : Subgroup G} {n r : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {π : Fin (r + 1) ≃ Fin n} {κ : normOmega E₁ r →* G}
    {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E₁ Bs X eta π κ χ)
    (hr : 2 ≤ r)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (u : Fin r → Multiplicative (ZMod 3)) :
    κ (normPlaneTorus E₁ hr (by decide : 3 ∣ 2 ^ 1 + 1) χ u) ∈ Bs :=
  hframe.normPlaneTorus_mem_Bs_of_dvd hr (by decide) hSC u

theorem GGSecFiveBPermOmKFrame.coords_normPlaneTorus
    {G : Type} [Group G] {Bs X : Subgroup G} {n r : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {π : Fin (r + 1) ≃ Fin n} {κ : normOmega E₁ r →* G}
    {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E₁ Bs X eta π κ χ)
    (hr : 2 ≤ r)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (u : Fin r → Multiplicative (ZMod 3)) (i : Fin r) :
    eta ⟨κ (normPlaneTorus E₁ hr (by decide : 3 ∣ 2 ^ 1 + 1) χ u),
        hframe.normPlaneTorus_mem_Bs hr hSC u⟩ (π i.castSucc) = u i :=
  hframe.coords_normPlaneTorus_of_dvd hr (by decide) hSC u i

end ActivePlaneTorus

end OrthogonalNeighbourFrameTransport

section AmbientBlockComm

theorem GGSecFiveBPermOmKFrame.blockComm
    {G : Type} [Group G] [Finite G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)} (hF : Nat.card F = 2)
    {B Bs L D J : Subgroup G} {x : G} {n r : ℕ} (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (S : Finset (Fin r)) (hS : S.card = 1 ∨ S.card = 2) :
    ggBlockComm Bs eta ((fun i : Fin r => π i.castSucc) '' (S : Set (Fin r))) =
      (normBlock E r S).map κ := by
  classical
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  let I : Set (Fin n) := (fun i : Fin r => π i.castSucc) '' (S : Set (Fin r))
  let H : Subgroup G := ggBsCoordZeroOn Bs eta I
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let A : Subgroup G := L ⊓ C
  let M : Subgroup (normOmega E r) := normBlock E r S
  let R : Subgroup G := M.map κ
  let W : Subgroup G := Bs ⊓ R
  let N : Subgroup G := ⁅A, A⁆
  let τ : (Fin r → Multiplicative (ZMod 3)) →* normOmega E r :=
    normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ
  let T : Subgroup (normOmega E r) :=
    (Subgroup.pi (S : Set (Fin r))
      (fun _ => (⊥ : Subgroup (Multiplicative (ZMod 3))))).map τ
  let CΩ : Subgroup (normOmega E r) := Subgroup.centralizer (T : Set (normOmega E r))
  have hproper : S ≠ Finset.univ := by
    intro h
    have hcard : S.card = r := by rw [h]; simp
    omega
  have hSne : S.Nonempty := Finset.card_pos.mp (by rcases hS with h1 | h2 <;> omega)
  have hi0 : i0 ∉ I := by
    intro hmem
    rw [show I = (fun i : Fin r => π i.castSucc) '' (S : Set (Fin r)) from rfl,
      Set.mem_image] at hmem
    obtain ⟨i, -, hpi'⟩ := hmem
    have hlast : Fin.last r = i.castSucc := π.injective (by rw [hpi, hpi'])
    exact (Fin.castSucc_lt_last i).ne hlast.symm
  have houtside : ∃ j : Fin n, j ≠ i0 ∧ j ∉ I := by
    obtain ⟨k, hk⟩ : ∃ k : Fin r, k ∉ S := by
      by_contra h
      exact hproper (Finset.eq_univ_iff_forall.mpr fun k => by
        by_contra hk
        exact h ⟨k, hk⟩)
    refine ⟨π k.castSucc, ?_, ?_⟩
    · intro h
      have hlast : Fin.last r = k.castSucc := π.injective (by rw [hpi, h])
      exact (Fin.castSucc_lt_last k).ne hlast.symm
    · intro hmem
      rw [show I = (fun i : Fin r => π i.castSucc) '' (S : Set (Fin r)) from rfl,
        Set.mem_image] at hmem
      obtain ⟨i, hi, hpi'⟩ := hmem
      have hik : i = k := Fin.castSucc_injective r (π.injective hpi')
      exact hk (hik ▸ hi)
  have hCnormL : C ≤ Subgroup.normalizer (L : Set G) := by
    simpa [C, H, I] using
      ggCentralizer_coordZeroOn_le_normalizer_of_bCoordinateBlock
        hcfg hZ hN eta i0 hLeta (S := I) hi0 houtside
  have hCnormA : C ≤ Subgroup.normalizer (A : Set G) := by
    have h := (le_inf hCnormL (Subgroup.le_normalizer (H := C))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := L) (K := C))
    simpa [A] using h
  have hA : A = CΩ.map κ := by
    simpa [A, C, H, CΩ, T, τ, I] using
      GGSecFiveBPermOmKFrame.inf_centralizer_coordZeroOn_eq_map
        (hframe := hframe) (hr := by omega) (hpq := by decide) (S := S)
  have hNative : ⁅CΩ, CΩ⁆ = M := by
    have h := commutator_centralizer_normPlaneTorus_eq_normBlock
      E hF hr χ hframe.2.2.1 S hS hproper
    simpa [CΩ, T, τ, M] using h
  have hDerived : N = R := by
    calc N = ⁅CΩ.map κ, CΩ.map κ⁆ := by
          rw [show N = ⁅A, A⁆ from rfl, hA]
      _ = (⁅CΩ, CΩ⁆).map κ := (Subgroup.map_commutator CΩ CΩ κ).symm
      _ = M.map κ := by rw [hNative]
      _ = R := rfl
  have hNnorm : C ≤ Subgroup.normalizer (N : Set G) := by
    intro c hc
    have hcA : c ∈ Subgroup.normalizer (A : Set G) := hCnormA hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hcA ⊢
    rw [show N = ⁅A, A⁆ from rfl, Subgroup.map_commutator, hcA]
  have hWN : W ≤ N := by
    change Bs ⊓ R ≤ N
    rw [← hDerived]
    exact inf_le_right
  have hNR : N ≤ R := hDerived.le
  have hRC : R ≤ C := by
    rw [← hDerived]
    change ⁅A, A⁆ ≤ C
    exact (Subgroup.commutator_le_self A).trans inf_le_right
  haveI hSimpleM : IsSimpleGroup ↥M := by
    simpa [M] using isSimpleGroup_normBlock E hr S hSne
  haveI hPerfectM : Group.IsPerfect ↥M := by
    simpa [M] using isPerfect_normBlock E hr S hSne
  let φ : ↥M →* ↥R :=
    { toFun := fun m => ⟨κ (m : normOmega E r), Subgroup.mem_map_of_mem κ m.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hφinj : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    exact hframe.1 (congrArg Subtype.val h)
  have hφsurj : Function.Surjective φ := by
    intro r
    obtain ⟨m, hm, hmr⟩ := Subgroup.mem_map.mp r.2
    exact ⟨⟨m, hm⟩, Subtype.ext hmr⟩
  let eMR : ↥M ≃* ↥R := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  haveI hSimpleR : IsSimpleGroup ↥R := eMR.symm.isSimpleGroup
  haveI hPerfectR : Group.IsPerfect ↥R :=
    Group.IsPerfect.ofSurjective (f := eMR.toMonoidHom) eMR.surjective
  have hcenterR : Subgroup.center ↥R = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative ↥R)
  obtain ⟨i, hiS⟩ := hSne
  let u : Fin r → Multiplicative (ZMod 3) :=
    Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3))
  have hu : ∀ j, j ∉ S → u j = 1 := by
    intro j hj
    dsimp [u]
    rw [Pi.mulSingle_eq_of_ne]
    intro hji
    exact hj (hji ▸ hiS)
  have hτM : normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ u ∈ M :=
    normPlaneTorus_mem_normBlock_of_support E (by omega : 2 ≤ r) χ S u hu
  let w : G := κ (normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ u)
  have hwBs : w ∈ Bs :=
    hframe.normPlaneTorus_mem_Bs (hr := by omega) hSC u
  have hwR : w ∈ R := Subgroup.mem_map_of_mem κ hτM
  have hwW : w ∈ W := ⟨hwBs, hwR⟩
  have hw_ne_one : w ≠ 1 := by
    intro hw1
    have hτ1 : normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ u = 1 := by
      apply hframe.1
      simpa [w] using hw1
    have hu1 : u = 1 := by
      apply normPlaneTorus_injective E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) hframe.2.2.1
      simpa using hτ1
    have hui : u i = 1 := by simpa using congrFun hu1 i
    have hof : Multiplicative.ofAdd (1 : ZMod 3) = 1 := by simpa [u] using hui
    have h10 : (1 : ZMod 3) = 0 := by simpa using congrArg Multiplicative.toAdd hof
    exact one_ne_zero h10
  have hWne : W ≠ ⊥ := by
    intro hbot
    exact hw_ne_one (Subgroup.mem_bot.mp (hbot ▸ hwW))
  have hRW : R ≤ ⁅R, W⁆ :=
    le_commutator_of_isSimpleGroup_of_ne_bot inf_le_right hcenterR hWne
  have hgen : ∀ e ∈ Bs, ∃ h ∈ H, ∃ w ∈ W, e = h * w := by
    intro e he
    let b : ↥Bs := ⟨e, he⟩
    let uS : Fin r → Multiplicative (ZMod 3) :=
      fun i => if i ∈ S then eta b (π i.castSucc) else 1
    have huS : ∀ i, i ∉ S → uS i = 1 := by intro i hi; simp [uS, hi]
    let w : G := κ (normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ uS)
    have hwBs : w ∈ Bs :=
      hframe.normPlaneTorus_mem_Bs (hr := by omega) hSC uS
    have hτM : normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ uS ∈ M :=
      normPlaneTorus_mem_normBlock_of_support E (by omega : 2 ≤ r) χ S uS huS
    have hwR : w ∈ R := Subgroup.mem_map_of_mem κ hτM
    have hwW : w ∈ W := ⟨hwBs, hwR⟩
    have hwcoord : ∀ i, eta ⟨w, hwBs⟩ (π i.castSucc) = uS i := by
      intro i
      exact hframe.coords_normPlaneTorus (hr := by omega) (hSC := hSC) (u := uS) i
    have hbwBs : e * w⁻¹ ∈ Bs := Bs.mul_mem he (Bs.inv_mem hwBs)
    have hbwH : e * w⁻¹ ∈ H := by
      rw [show H = ggBsCoordZeroOn Bs eta I from rfl, mem_ggBsCoordZeroOn]
      refine ⟨hbwBs, ?_⟩
      rintro j ⟨i, hiS, rfl⟩
      have hbw_eq : (⟨e * w⁻¹, hbwBs⟩ : ↥Bs) = b * (⟨w, hwBs⟩ : ↥Bs)⁻¹ := by
        ext; rfl
      rw [hbw_eq, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hwcoord i]
      have hiS' : i ∈ S := by simpa using hiS
      simp [uS, hiS']
    refine ⟨e * w⁻¹, hbwH, w, hwW, by group⟩
  have hcomm := ggCommutator_centralizer_eq_of_mul
    (E := Bs) (H := H) (W := W) (N := N) (R := R)
    hgen inf_le_left hNnorm hWN hNR hRC hRW
  simpa [ggBlockComm, H, I, R, M] using hcomm

end AmbientBlockComm

section PermutationAction

theorem GGSecFiveBPermOmKFrame.conj_normPerm_eq_of_dvd
    {G : Type} [Group G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {f p : ℕ} {E : QuadExt F K (unitaryInvolution K 2 f)}
    {Bs L : Subgroup G} {n r : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Equiv.Perm (Fin r)) (b : ↥Bs) :
    (κ (normPerm E hr σ) : G) * (b : G) * (κ (normPerm E hr σ))⁻¹ =
      (b : G) *
        (κ (normPlaneTorus E (by omega : 2 ≤ r) hpq χ
          (fun i => eta b (π i.castSucc))))⁻¹ *
        κ (normPlaneTorus E (by omega : 2 ≤ r) hpq χ
          (fun i => eta b (π (σ⁻¹ i).castSucc))) := by
  classical
  let τ : (Fin r → Multiplicative (ZMod p)) →* normOmega E r :=
    normPlaneTorus E (by omega : 2 ≤ r) hpq χ
  let u : Fin r → Multiplicative (ZMod p) := fun i => eta b (π i.castSucc)
  let t : G := κ (τ u)
  let a : G := κ (normPerm E hr σ)
  let v : Fin r → Multiplicative (ZMod p) := fun i => u (σ⁻¹ i)
  let tv : G := κ (τ v)
  have htBs : t ∈ Bs :=
    hframe.normPlaneTorus_mem_Bs_of_dvd (hr := by omega) (hpq := hpq) (hSC := hSC) u
  have htvBs : tv ∈ Bs :=
    hframe.normPlaneTorus_mem_Bs_of_dvd (hr := by omega) (hpq := hpq) (hSC := hSC) v
  have hz : ∀ s : normOmega E r,
      (t⁻¹ * (b : G)) * κ s = κ s * (t⁻¹ * (b : G)) := by
    intro s
    have hbconj := GGSecFiveBPermOmKFrame.conj_eq_normPlaneTorus
      (hr := by omega) (hpq := hpq) (hframe := hframe) b s
    have hbt : (b : G) * κ s * (b : G)⁻¹ = t * κ s * t⁻¹ := by
      simpa [t, u, τ, map_mul, map_inv] using hbconj
    calc (t⁻¹ * (b : G)) * κ s = t⁻¹ * ((b : G) * κ s * (b : G)⁻¹) * (b : G) := by group
      _ = t⁻¹ * (t * κ s * t⁻¹) * (b : G) := by rw [hbt]
      _ = κ s * (t⁻¹ * (b : G)) := by group
  have haz : a * (t⁻¹ * (b : G)) = (t⁻¹ * (b : G)) * a := by
    have := hz (normPerm E hr σ)
    simpa [a] using this.symm
  have hza_inv : (t⁻¹ * (b : G)) * a⁻¹ = a⁻¹ * (t⁻¹ * (b : G)) := by
    calc (t⁻¹ * (b : G)) * a⁻¹ = a⁻¹ * (a * (t⁻¹ * (b : G))) * a⁻¹ := by group
      _ = a⁻¹ * ((t⁻¹ * (b : G)) * a) * a⁻¹ := by rw [haz]
      _ = a⁻¹ * (t⁻¹ * (b : G)) := by group
  have hnat : a * t * a⁻¹ = tv := by
    have h := congrArg κ (normPerm_conj_normPlaneTorus (E := E) hr hpq χ σ u)
    simpa [a, t, tv, v, u, τ, map_mul, map_inv] using h
  have hbs_comm : ∀ x y : ↥Bs, x * y = y * x := fun x y =>
    eta.injective (by rw [map_mul, map_mul, mul_comm])
  have hreorder : tv * t⁻¹ * (b : G) = (b : G) * t⁻¹ * tv := by
    let tbs : ↥Bs := ⟨t, htBs⟩
    let tvbs : ↥Bs := ⟨tv, htvBs⟩
    letI : CommGroup ↥Bs := { (inferInstance : Group ↥Bs) with mul_comm := hbs_comm }
    have hbs : tvbs * tbs⁻¹ * b = b * tbs⁻¹ * tvbs := by ac_rfl
    simpa [tbs, tvbs] using congrArg Subtype.val hbs
  calc a * (b : G) * a⁻¹ = a * (t * (t⁻¹ * (b : G))) * a⁻¹ := by group
    _ = (a * t) * ((t⁻¹ * (b : G)) * a⁻¹) := by group
    _ = (a * t) * (a⁻¹ * (t⁻¹ * (b : G))) := by rw [hza_inv]
    _ = (a * t * a⁻¹) * (t⁻¹ * (b : G)) := by group
    _ = tv * (t⁻¹ * (b : G)) := by rw [hnat]
    _ = tv * t⁻¹ * (b : G) := by group
    _ = (b : G) * t⁻¹ * tv := hreorder

theorem GGSecFiveBPermOmKFrame.conj_normPerm_eq
    {G : Type} [Group G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)}
    {Bs L : Subgroup G} {n r : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (hr : 3 ≤ r)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (σ : Equiv.Perm (Fin r)) (b : ↥Bs) :
    (κ (normPerm E hr σ) : G) * (b : G) * (κ (normPerm E hr σ))⁻¹ =
      (b : G) *
        (κ (normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ
          (fun i => eta b (π i.castSucc))))⁻¹ *
        κ (normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ
          (fun i => eta b (π (σ⁻¹ i).castSucc))) :=
  hframe.conj_normPerm_eq_of_dvd hr (by decide) hSC σ b

theorem GGSecFiveBPermOmKFrame.normPerm_mem_normalizer_of_dvd
    {G : Type} [Group G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {f p : ℕ} {E : QuadExt F K (unitaryInvolution K 2 f)}
    {Bs L : Subgroup G} {n r : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Equiv.Perm (Fin r)) :
    κ (normPerm E hr σ) ∈ Subgroup.normalizer (Bs : Set G) := by
  classical
  let a : G := κ (normPerm E hr σ)
  have hconj_mem : ∀ (τ : Equiv.Perm (Fin r)) (x : ↥Bs),
      κ (normPerm E hr τ) * (x : G) * (κ (normPerm E hr τ))⁻¹ ∈ Bs := by
    intro τ x
    have h := hframe.conj_normPerm_eq_of_dvd (hr := hr) (hpq := hpq) (hSC := hSC) τ x
    rw [h]
    let u : Fin r → Multiplicative (ZMod p) := fun i => eta x (π i.castSucc)
    have ht : κ (normPlaneTorus E (by omega : 2 ≤ r) hpq χ u) ∈ Bs :=
      hframe.normPlaneTorus_mem_Bs_of_dvd (hr := by omega) (hpq := hpq) (hSC := hSC) u
    have hv : κ (normPlaneTorus E (by omega : 2 ≤ r) hpq χ
        (fun i => u (τ⁻¹ i))) ∈ Bs :=
      hframe.normPlaneTorus_mem_Bs_of_dvd (hr := by omega) (hpq := hpq) (hSC := hSC) _
    simpa [u] using Bs.mul_mem (Bs.mul_mem x.2 (Bs.inv_mem ht)) hv
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact hconj_mem σ ⟨b, hb⟩
  · intro hb
    have hb' := hconj_mem σ⁻¹ ⟨a * (b : G) * a⁻¹, hb⟩
    have ha_inv : κ (normPerm E hr σ⁻¹) = a⁻¹ := by
      calc κ (normPerm E hr σ⁻¹) = κ ((normPerm E hr σ)⁻¹) := by rw [map_inv]
        _ = (κ (normPerm E hr σ))⁻¹ := by rw [map_inv]
        _ = a⁻¹ := by rfl
    rw [ha_inv] at hb'
    have hb'' : b ∈ Bs := by
      convert hb' using 1
      group
    exact hb''

theorem GGSecFiveBPermOmKFrame.normPerm_mem_normalizer
    {G : Type} [Group G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)}
    {Bs L : Subgroup G} {n r : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (hr : 3 ≤ r)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (σ : Equiv.Perm (Fin r)) :
    κ (normPerm E hr σ) ∈ Subgroup.normalizer (Bs : Set G) :=
  hframe.normPerm_mem_normalizer_of_dvd hr (by decide) hSC σ

theorem GGSecFiveBPermOmKFrame.coords_normPerm_of_dvd
    {G : Type} [Group G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {f p : ℕ} {E : QuadExt F K (unitaryInvolution K 2 f)}
    {Bs L : Subgroup G} {n r : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (σ : Equiv.Perm (Fin r)) (b : ↥Bs) (i : Fin r) :
    eta (ggConjAut Bs
        (hframe.normPerm_mem_normalizer_of_dvd (hr := hr) (hpq := hpq) (hSC := hSC) σ) b)
        (π i.castSucc) = eta b (π (σ⁻¹ i).castSucc) := by
  classical
  let a : G := κ (normPerm E hr σ)
  have ha : a ∈ Subgroup.normalizer (Bs : Set G) :=
    hframe.normPerm_mem_normalizer_of_dvd (hr := hr) (hpq := hpq) (hSC := hSC) σ
  let τ : (Fin r → Multiplicative (ZMod p)) →* normOmega E r :=
    normPlaneTorus E (by omega : 2 ≤ r) hpq χ
  let u : Fin r → Multiplicative (ZMod p) := fun i => eta b (π i.castSucc)
  let t : G := κ (τ u)
  let v : Fin r → Multiplicative (ZMod p) := fun i => u (σ⁻¹ i)
  let tv : G := κ (τ v)
  have htBs : t ∈ Bs :=
    hframe.normPlaneTorus_mem_Bs_of_dvd (hr := by omega) (hpq := hpq) (hSC := hSC) u
  have htvBs : tv ∈ Bs :=
    hframe.normPlaneTorus_mem_Bs_of_dvd (hr := by omega) (hpq := hpq) (hSC := hSC) v
  have hconj := hframe.conj_normPerm_eq_of_dvd (hr := hr) (hpq := hpq) (hSC := hSC) σ b
  have hsub : ggConjAut Bs ha b = b * (⟨t, htBs⟩ : ↥Bs)⁻¹ * ⟨tv, htvBs⟩ := by
    ext
    simpa [a, t, tv, u, v, ggConjAut_apply] using hconj
  change eta (ggConjAut Bs ha b) (π i.castSucc) = eta b (π (σ⁻¹ i).castSucc)
  have htcoord : eta ⟨t, htBs⟩ (π i.castSucc) = u i :=
    hframe.coords_normPlaneTorus_of_dvd (hr := by omega) (hpq := hpq) (hSC := hSC) (u := u) i
  have hvcoord : eta ⟨tv, htvBs⟩ (π i.castSucc) = v i :=
    hframe.coords_normPlaneTorus_of_dvd (hr := by omega) (hpq := hpq) (hSC := hSC) (u := v) i
  calc eta (ggConjAut Bs ha b) (π i.castSucc)
      = eta (b * (⟨t, htBs⟩ : ↥Bs)⁻¹ * ⟨tv, htvBs⟩) (π i.castSucc) := by rw [hsub]
    _ = eta b (π i.castSucc) * (eta ⟨t, htBs⟩ (π i.castSucc))⁻¹ *
          eta ⟨tv, htvBs⟩ (π i.castSucc) := by
          simp [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply]
    _ = u i * (u i)⁻¹ * v i := by rw [htcoord, hvcoord]
    _ = eta b (π (σ⁻¹ i).castSucc) := by simp [u, v]

theorem GGSecFiveBPermOmKFrame.coords_normPerm
    {G : Type} [Group G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)}
    {Bs L : Subgroup G} {n r : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (hr : 3 ≤ r)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (σ : Equiv.Perm (Fin r)) (b : ↥Bs) (i : Fin r) :
    eta (ggConjAut Bs (hframe.normPerm_mem_normalizer (hr := hr) (hSC := hSC) σ) b)
        (π i.castSucc) = eta b (π (σ⁻¹ i).castSucc) :=
  hframe.coords_normPerm_of_dvd hr (by decide) hSC σ b i

theorem GGSecFiveBPermOmKFrame.normPlaneTorus_coord_last
    {G : Type} [Group G] [Finite G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)}
    {B Bs L D J : Subgroup G} {x : G} {n r : ℕ} (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (v : Fin r → Multiplicative (ZMod 3)) :
    eta ⟨κ (normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ v),
        hframe.normPlaneTorus_mem_Bs (hr := by omega) (hSC := hcfg.2.1.2.2.2) v⟩ i0 = 1 := by
  have hSC := hcfg.2.1.2.2.2
  let b : ↥Bs :=
    ⟨κ (normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ v),
      hframe.normPlaneTorus_mem_Bs (hr := by omega) hSC v⟩
  have hbL : (b : G) ∈ L := by
    rw [← hframe.2.1]
    exact ⟨_, rfl⟩
  exact (ggBstar_mem_iff_coord_eq_one hcfg hZ hN eta i0 hLeta b).mp hbL

theorem GGSecFiveBPermOmKFrame.coords_normPerm_last
    {G : Type} [Group G] [Finite G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)}
    {B Bs L D J : Subgroup G} {x : G} {n r : ℕ} (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (σ : Equiv.Perm (Fin r)) (b : ↥Bs) :
    eta (ggConjAut Bs (hframe.normPerm_mem_normalizer (hr := hr)
        (hSC := hcfg.2.1.2.2.2) σ) b) i0 = eta b i0 := by
  classical
  have hSC := hcfg.2.1.2.2.2
  let a : G := κ (normPerm E hr σ)
  have ha : a ∈ Subgroup.normalizer (Bs : Set G) :=
    hframe.normPerm_mem_normalizer (hr := hr) hSC σ
  let τ : (Fin r → Multiplicative (ZMod 3)) →* normOmega E r :=
    normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ
  let u : Fin r → Multiplicative (ZMod 3) := fun i => eta b (π i.castSucc)
  let t : G := κ (τ u)
  let v : Fin r → Multiplicative (ZMod 3) := fun i => u (σ⁻¹ i)
  let tv : G := κ (τ v)
  have htBs : t ∈ Bs := hframe.normPlaneTorus_mem_Bs (hr := by omega) hSC u
  have htvBs : tv ∈ Bs := hframe.normPlaneTorus_mem_Bs (hr := by omega) hSC v
  have hconj := hframe.conj_normPerm_eq (hr := hr) (hSC := hSC) σ b
  have hsub : ggConjAut Bs ha b = b * (⟨t, htBs⟩ : ↥Bs)⁻¹ * ⟨tv, htvBs⟩ := by
    ext
    simpa [a, t, tv, u, v, ggConjAut_apply] using hconj
  have htlast : eta ⟨t, htBs⟩ i0 = 1 :=
    hframe.normPlaneTorus_coord_last hr hcfg hZ hN hLeta u
  have hvlast : eta ⟨tv, htvBs⟩ i0 = 1 :=
    hframe.normPlaneTorus_coord_last hr hcfg hZ hN hLeta v
  change eta (ggConjAut Bs ha b) i0 = eta b i0
  calc eta (ggConjAut Bs ha b) i0
      = eta (b * (⟨t, htBs⟩ : ↥Bs)⁻¹ * ⟨tv, htvBs⟩) i0 := by rw [hsub]
    _ = eta b i0 * (eta ⟨t, htBs⟩ i0)⁻¹ * eta ⟨tv, htvBs⟩ i0 := by
          simp [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply]
    _ = eta b i0 := by simp [htlast, hvlast]

theorem GGSecFiveBPermOmKFrame.congr_normPerm
    {G : Type} [Group G] [Finite G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)}
    {B Bs L D J : Subgroup G} {x : G} {n r : ℕ} (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (σ : Equiv.Perm (Fin r)) :
    let ι : Fin r ↪ Fin n := (Fin.castSuccEmb (n := r)).trans π.toEmbedding
    MulAut.congr eta (ggConjAut Bs (hframe.normPerm_mem_normalizer
        (hr := hr) (hSC := hcfg.2.1.2.2.2) σ)) =
      SpCoord.permAut (Equiv.Perm.viaEmbeddingHom ι σ) := by
  classical
  let ι : Fin r ↪ Fin n := (Fin.castSuccEmb (n := r)).trans π.toEmbedding
  apply MulEquiv.ext
  intro v
  obtain ⟨b, rfl⟩ := eta.surjective v
  have hcongr : (MulAut.congr eta (ggConjAut Bs (hframe.normPerm_mem_normalizer
      (hr := hr) (hSC := hcfg.2.1.2.2.2) σ))) (eta b) =
      eta (ggConjAut Bs (hframe.normPerm_mem_normalizer
        (hr := hr) (hSC := hcfg.2.1.2.2.2) σ) b) := by
    funext j
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  funext j
  obtain ⟨k, rfl⟩ := π.surjective j
  rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
  · rw [hcongr, hframe.coords_normPerm (hr := hr) (hSC := hcfg.2.1.2.2.2) σ b i]
    rw [SpCoord.permAut_apply]
    have hinv : (Equiv.Perm.viaEmbeddingHom ι σ)⁻¹ =
        Equiv.Perm.viaEmbeddingHom ι σ⁻¹ := by rw [map_inv]
    rw [hinv, Equiv.Perm.viaEmbeddingHom_apply]
    change eta b (π (σ⁻¹ i).castSucc) =
      eta b ((Equiv.Perm.viaEmbedding σ⁻¹ ι) (ι i))
    rw [Equiv.Perm.viaEmbedding_apply]
    rfl
  · rw [hcongr, hpi,
      GGSecFiveBPermOmKFrame.coords_normPerm_last (hframe := hframe)
        (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN) (hLeta := hLeta)
        (hpi := hpi) (σ := σ) (b := b)]
    rw [SpCoord.permAut_apply]
    have hnot : i0 ∉ Set.range ι := by
      rintro ⟨i, hi⟩
      have hi' : π i.castSucc = i0 := by simpa [ι] using hi
      have hlast : i.castSucc = Fin.last r := π.injective (by rw [hi', hpi])
      exact Fin.castSucc_ne_last i hlast
    have hinv : (Equiv.Perm.viaEmbeddingHom ι σ)⁻¹ =
        Equiv.Perm.viaEmbeddingHom ι σ⁻¹ := by rw [map_inv]
    rw [hinv, Equiv.Perm.viaEmbeddingHom_apply]
    change eta b i0 = eta b ((Equiv.Perm.viaEmbedding σ⁻¹ ι) i0)
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem (e := σ⁻¹) (ι := ι) (x := i0) hnot]

theorem GGSecFiveBPermOmKFrame.normPerm_swap_mem_ggBlockComm
    {G : Type} [Group G] [Finite G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)} (hF : Nat.card F = 2)
    {B Bs L D J : Subgroup G} {x : G} {n r : ℕ} (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (i j : Fin r) :
    κ (normPerm E hr (Equiv.swap i j)) ∈
      ggBlockComm Bs eta ({π i.castSucc, π j.castSucc} : Set (Fin n)) := by
  classical
  have hS : ({i, j} : Finset (Fin r)).card = 1 ∨
      ({i, j} : Finset (Fin r)).card = 2 := by
    by_cases hij : i = j
    · left; simp [hij]
    · right; simp [hij]
  have hblock := GGSecFiveBPermOmKFrame.blockComm
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (S := {i, j}) (hS := hS)
  have hmem : κ (normPerm E hr (Equiv.swap i j)) ∈
      (normBlock E r ({i, j} : Finset (Fin r))).map κ :=
    Subgroup.mem_map_of_mem _ (normPerm_swap_mem_normBlock (E := E) hr i j)
  have hblock' : ggBlockComm Bs eta ({π i.castSucc, π j.castSucc} : Set (Fin n)) =
      (normBlock E r ({i, j} : Finset (Fin r))).map κ := by
    simpa [Set.image_pair] using hblock
  rw [hblock']
  exact hmem

theorem GGSecFiveBPermOmKFrame.blockComm_commute_normPerm
    {G : Type} [Group G] [Finite G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)} (hF : Nat.card F = 2)
    {B Bs L D J : Subgroup G} {x : G} {n r : ℕ} (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    {i j : Fin r} (hij : i ≠ j) (σ : Equiv.Perm (Fin r)) (hi : σ i = i) (hj : σ j = j) :
    ∀ x ∈ ggBlockComm Bs eta
        ((fun k : Fin r => π k.castSucc) '' (({i, j} : Finset (Fin r)) : Set (Fin r))),
      κ (normPerm E hr σ) * x = x * κ (normPerm E hr σ) := by
  intro x hx
  have hS : ({i, j} : Finset (Fin r)).card = 1 ∨ ({i, j} : Finset (Fin r)).card = 2 :=
    Or.inr (by simp [hij])
  have hblock := GGSecFiveBPermOmKFrame.blockComm
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (S := {i, j}) (hS := hS)
  have hx' : x ∈ (normBlock E r {i, j}).map κ := by
    simpa only [hblock] using hx
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx'
  have hcomm := normPerm_commute_normBlock_pair E hr hij σ ⟨m, hm⟩ hi hj
  simpa [map_mul] using congrArg κ hcomm

end PermutationAction

end CFSG.StandardType

end
