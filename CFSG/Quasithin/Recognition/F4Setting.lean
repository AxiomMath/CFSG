module

public import CFSG.Quasithin.Recognition.F4Transfer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

structure LieSetting where
  α : RankTwoAmalgam.{u}
  Yb : Type w
  [grp : Group Yb]
  [fin : Finite Yb]
  ι : α.Completion Yb
  hι : ι.IsFaithful
  N : Subgroup ι.G0
  hN : N.Normal
  p : ℕ
  hp : p.Prime
  m : ℕ
  hm : 3 ≤ m

attribute [instance] LieSetting.grp LieSetting.fin

namespace LieSetting

variable (S : LieSetting.{u, w})

@[expose] noncomputable def Qbar (u : S.ι.Γ) : Subgroup S.ι.G0 := pCoreOf S.p (S.N ⊓ stv S.ι u)

theorem Qbar_le_stv (u : S.ι.Γ) : S.Qbar u ≤ stv S.ι u :=
  (pCoreOf_le S.p _).trans inf_le_right

theorem conjSub_normal {H : Type*} [Group H] {K : Subgroup H} (hK : K.Normal) (g : H) :
    conjSub g K = K := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro h
    have := hK.conj_mem _ h g
    simpa [mul_assoc] using this
  · intro h
    have := hK.conj_mem _ h g⁻¹
    simpa [mul_assoc] using this

theorem Qbar_smul (g : S.ι.G0) (u : S.ι.Γ) : S.Qbar (g • u) = conjSub g (S.Qbar u) := by
  have h1 : S.N ⊓ stv S.ι (g • u) = conjSub g (S.N ⊓ stv S.ι u) := by
    rw [stv_smul, conjSub_inf, conjSub_normal S.hN g]
  unfold Qbar
  rw [h1]
  exact pCoreOf_map_mulEquiv S.p (MulAut.conj g) _

theorem conjSub_Qbar {u : S.ι.Γ} {h : S.ι.G0} (hh : h ∈ stv S.ι u) :
    conjSub h (S.Qbar u) = S.Qbar u := by
  rw [← Qbar_smul, MulAction.mem_stabilizer_iff.mp hh]

theorem conjSub_map {A H : Type*} [Group A] [Group H] (f : A →* H) (a : A) (Q : Subgroup A) :
    conjSub (f a) (Q.map f) = (conjSub a Q).map f := by
  ext x
  rw [mem_conjSub, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, hqx⟩
    refine ⟨a * q * a⁻¹, ?_, ?_⟩
    · rw [mem_conjSub]
      have e : a⁻¹ * (a * q * a⁻¹) * a = q := by group
      rw [e]
      exact hq
    · rw [map_mul, map_mul, map_inv, hqx]
      group
  · rintro ⟨y, hy, rfl⟩
    rw [mem_conjSub] at hy
    exact ⟨a⁻¹ * y * a, hy, by rw [map_mul, map_mul, map_inv]⟩

@[expose] noncomputable def Qb1 : Subgroup S.α.G1 := (S.Qbar S.ι.xv).comap (f1 (c := S.ι))

@[expose] noncomputable def Qb2 : Subgroup S.α.G2 := (S.Qbar S.ι.lv).comap (f2 (c := S.ι))

@[expose] noncomputable def Qx {Y : Type w'} [Group Y] (β : S.α.Completion Y) : Subgroup β.G0 :=
  S.Qb1.map (f1 (c := β))

@[expose] noncomputable def Ql {Y : Type w'} [Group Y] (β : S.α.Completion Y) : Subgroup β.G0 :=
  S.Qb2.map (f2 (c := β))

theorem Qb1_normal : S.Qb1.Normal := by
  refine ⟨fun a ha b => ?_⟩
  show f1 (c := S.ι) (b * a * b⁻¹) ∈ S.Qbar S.ι.xv
  rw [map_mul, map_mul, map_inv]
  have hb : f1 (c := S.ι) b ∈ stv S.ι S.ι.xv :=
    MulAction.mem_stabilizer_iff.mpr (f1_smul_xv b)
  have h1 : conjSub (f1 (c := S.ι) b) (S.Qbar S.ι.xv) = S.Qbar S.ι.xv :=
    S.conjSub_Qbar hb
  have h2 : f1 (c := S.ι) a ∈ S.Qbar S.ι.xv := ha
  have := mul_mem_conjSub (g := f1 (c := S.ι) b) h2
  rwa [h1] at this

theorem Qb2_normal : S.Qb2.Normal := by
  refine ⟨fun a ha b => ?_⟩
  show f2 (c := S.ι) (b * a * b⁻¹) ∈ S.Qbar S.ι.lv
  rw [map_mul, map_mul, map_inv]
  have hb : f2 (c := S.ι) b ∈ stv S.ι S.ι.lv :=
    MulAction.mem_stabilizer_iff.mpr (f2_smul_lv b)
  have h1 : conjSub (f2 (c := S.ι) b) (S.Qbar S.ι.lv) = S.Qbar S.ι.lv :=
    S.conjSub_Qbar hb
  have h2 : f2 (c := S.ι) a ∈ S.Qbar S.ι.lv := ha
  have := mul_mem_conjSub (g := f2 (c := S.ι) b) h2
  rwa [h1] at this

structure Facts45L (S : LieSetting.{u, w}) : Prop where
  thick1 : 2 ≤ S.α.qOne
  thick2 : 2 ≤ S.α.qTwo
  poly : IsGenPolygon S.ι.graph S.m
  trans : ∀ u : S.ι.Γ, S.ι.PathTrans u (S.m + 1)
  compl : ∀ u v : S.ι.Γ, S.ι.graph.dist u v = S.m →
    IsComplementIn (stv S.ι u ⊓ stv S.ι v) (S.Qbar u) (stv S.ι u)
  Qle : ∀ u w : S.ι.Γ, S.ι.graph.Adj u w → S.Qbar u ≤ stv S.ι w

theorem Qx_normalized {Y : Type w'} [Group Y] (β : S.α.Completion Y) :
    QNormalized (S.Qx β) (S.Ql β) := by
  intro b h hh
  cases b
  · have hh' : h ∈ stv β β.xv := MulAction.mem_stabilizer_iff.mpr hh
    obtain ⟨a0, rfl⟩ := stv_xv_le_range_f1 β hh'
    show conjSub (f1 (c := β) a0) (S.Qx β) = S.Qx β
    unfold Qx
    rw [conjSub_map, conjSub_normal S.Qb1_normal]
  · have hh' : h ∈ stv β β.lv := MulAction.mem_stabilizer_iff.mpr hh
    obtain ⟨a0, rfl⟩ := stv_lv_le_range_f2 β hh'
    show conjSub (f2 (c := β) a0) (S.Ql β) = S.Ql β
    unfold Ql
    rw [conjSub_map, conjSub_normal S.Qb2_normal]

theorem Facts45L.ofBase (thick1 : 2 ≤ S.α.qOne) (thick2 : 2 ≤ S.α.qTwo)
    (poly : IsGenPolygon S.ι.graph S.m)
    (transX : S.ι.PathTrans S.ι.xv (S.m + 1)) (transL : S.ι.PathTrans S.ι.lv (S.m + 1))
    (complX : ∀ v : S.ι.Γ, S.ι.graph.dist S.ι.xv v = S.m →
      IsComplementIn (stv S.ι S.ι.xv ⊓ stv S.ι v) (S.Qbar S.ι.xv) (stv S.ι S.ι.xv))
    (complL : ∀ v : S.ι.Γ, S.ι.graph.dist S.ι.lv v = S.m →
      IsComplementIn (stv S.ι S.ι.lv ⊓ stv S.ι v) (S.Qbar S.ι.lv) (stv S.ι S.ι.lv))
    (QleX : ∀ w : S.ι.Γ, S.ι.graph.Adj S.ι.xv w → S.Qbar S.ι.xv ≤ stv S.ι w)
    (QleL : ∀ w : S.ι.Γ, S.ι.graph.Adj S.ι.lv w → S.Qbar S.ι.lv ≤ stv S.ι w) :
    S.Facts45L := by
  have complB : ∀ (b : Bool) (v : S.ι.Γ), S.ι.graph.dist (S.ι.baseVert b) v = S.m →
      IsComplementIn (stv S.ι (S.ι.baseVert b) ⊓ stv S.ι v) (S.Qbar (S.ι.baseVert b))
        (stv S.ι (S.ι.baseVert b)) := by
    intro b v hv
    cases b
    · exact complX v hv
    · exact complL v hv
  have QleB : ∀ (b : Bool) (w : S.ι.Γ), S.ι.graph.Adj (S.ι.baseVert b) w →
      S.Qbar (S.ι.baseVert b) ≤ stv S.ι w := by
    intro b w hw
    cases b
    · exact QleX w hw
    · exact QleL w hw
  refine ⟨thick1, thick2, poly, fun u => pathTrans_of_base S.ι transX transL u, ?_, ?_⟩
  · intro u v huv
    obtain ⟨g, hg⟩ := exists_smul_eq_baseVert S.ι u
    have hv' : S.ι.graph.dist (S.ι.baseVert (CosetGeom.vtype u)) (g⁻¹ • v) = S.m := by
      have h1 : S.ι.graph.dist (g • S.ι.baseVert (CosetGeom.vtype u)) (g • (g⁻¹ • v)) =
          S.ι.graph.dist (S.ι.baseVert (CosetGeom.vtype u)) (g⁻¹ • v) :=
        CosetGeom.dist_smul g _ _
      rw [hg, smul_inv_smul] at h1
      rw [← h1]
      exact huv
    have h3 := (IsComplementIn.conjSub_iff g).mpr (complB _ _ hv')
    rw [conjSub_inf, ← stv_smul, ← stv_smul, ← Qbar_smul, hg, smul_inv_smul] at h3
    exact h3
  · intro u w huw
    obtain ⟨g, hg⟩ := exists_smul_eq_baseVert S.ι u
    have hadj : S.ι.graph.Adj (S.ι.baseVert (CosetGeom.vtype u)) (g⁻¹ • w) := by
      have := (GraphAction.adj_smul g⁻¹ u w).mpr huw
      rwa [show g⁻¹ • u = S.ι.baseVert (CosetGeom.vtype u) from
        inv_smul_eq_iff.mpr hg.symm] at this
    have h2 := conjSub_mono g (QleB _ _ hadj)
    rw [← Qbar_smul, ← stv_smul, hg, smul_inv_smul] at h2
    exact h2

end LieSetting

end CFSG.Quasithin
