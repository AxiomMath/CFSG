module

public import CFSG.Quasithin.Recognition.F4Setting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] (c : α.Completion Y)

structure TransComp (m : ℕ) : Prop where
  faithful : c.IsFaithful
  thick1 : 2 ≤ α.qOne
  thick2 : 2 ≤ α.qTwo
  trans : ∀ a : c.Γ, c.PathTrans a (m + 1)
  hm : 1 ≤ m

namespace TransComp

variable {c} {m : ℕ} (T : TransComp c m)

include T

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  exists_nbr_ne T.faithful T.thick1 T.thick2

theorem f35 {a : c.Γ} {p : GPath c.graph (m + 1)} (hp : p ∈ GPath.nbPaths c.graph a (m + 1)) :
    GPath.F35Conclusion c.graph c.G0 a m p :=
  GPath.lemma_F35 T.hval (T.trans a) (CosetGeom.connected rfl)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) T.hm hp

theorem dist_nbPath {n : ℕ} (hn : n ≤ m) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) : c.graph.dist a (p n) = n := by
  obtain ⟨r, hr, -⟩ := GPath.exists_extend_to T.hval (Nat.le_succ_of_le hn) hp
  exact (T.f35 hr).2.1 n hn p hp

theorem unique_geod {n : ℕ} (hn : n < m) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) {q : GPath c.graph n} (hq0 : q 0 = a)
    (hqn : q n = p n) (hqg : q.IsGeodesic) : q = p := by
  obtain ⟨r, hr, hrp⟩ := GPath.exists_extend_to T.hval (Nat.le_succ_of_le hn.le) hp
  have h := (T.f35 hr).2.2.2.1 n hn q hq0 (by
    rw [hqn, ← hrp, GPath.take_apply_of_le _ _ _ le_rfl]) hqg
  rw [h, hrp]

end TransComp

@[expose] def PhiII (c : α.Completion Y) (m : ℕ) (a b : c.Γ) : Prop :=
  (∀ y, c.graph.Adj b y → ∃! t : GPath c.graph m,
      t 0 = a ∧ t m = b ∧ t.IsGeodesic ∧ t (m - 1) = y) ∧
  (∀ t₁ t₂ t₃ t₄ : GPath c.graph m, t₁ ∈ c.geods m a b → t₂ ∈ c.geods m a b →
      t₃ ∈ c.geods m a b → t₄ ∈ c.geods m a b → t₁ ≠ t₂ → t₃ ≠ t₄ →
      ∃ g : c.G0, g • a = a ∧ g • b = b ∧ g • t₁ = t₃ ∧ g • t₂ = t₄) ∧
  (∀ y₁ y₂ z₁ z₂ : c.Γ, c.graph.Adj b y₁ → c.graph.Adj b y₂ → c.graph.Adj b z₁ →
      c.graph.Adj b z₂ → y₁ ≠ y₂ → z₁ ≠ z₂ →
      ∃ g : c.G0, g • a = a ∧ g • b = b ∧ g • y₁ = z₁ ∧ g • y₂ = z₂)

namespace TransComp

variable {c} {m : ℕ} (T : TransComp c m)

include T

theorem alt {a : c.Γ} {p : GPath c.graph m} (hp : p ∈ GPath.nbPaths c.graph a m) :
    ((∃ v, m < c.graph.dist a v) ∧
      ∀ t : GPath c.graph m, t 0 = a → t m = p m → t.IsGeodesic → t = p) ∨
    ((∀ v, c.graph.dist a v ≤ m) ∧ PhiII c m a (p m)) := by
  obtain ⟨r, hr, hrp⟩ := GPath.exists_extend_to T.hval (Nat.le_succ m) hp
  have hrm : r m = p m := by rw [← hrp, GPath.take_apply_of_le _ _ _ le_rfl]
  rcases (T.f35 hr).2.2.2.2.2.1 with h | h
  · left
    refine ⟨⟨r (m + 1), by rw [(h r hr).1]; omega⟩, ?_⟩
    intro t ht0 htm htg
    have := (h r hr).2 t ht0 htg (by rw [htm, hrm])
    rw [this, hrp]
  · right
    obtain ⟨hd, -, huniq, hnbtrans, hgtrans⟩ := h
    rw [hrm] at huniq hnbtrans hgtrans
    exact ⟨hd, huniq, fun t₁ t₂ t₃ t₄ h1 h2 h3 h4 hne hne' =>
      hgtrans t₁ t₂ t₃ t₄ h1 h2 h3 h4 hne hne', fun y₁ y₂ z₁ z₂ h1 h2 h3 h4 hne hne' =>
      hnbtrans y₁ y₂ z₁ z₂ h1 h2 h3 h4 hne hne'⟩

theorem exists_two_nbrs (v : c.Γ) : ∃ y₁ y₂, c.graph.Adj v y₁ ∧ c.graph.Adj v y₂ ∧ y₁ ≠ y₂ := by
  obtain ⟨y₁, h1⟩ := CosetGeom.exists_adj v
  obtain ⟨y₂, h2, hne, -⟩ := T.hval v y₁ y₁
  exact ⟨y₁, y₂, h1, h2, hne.symm⟩

theorem phiII_symm {a b : c.Γ} (h : PhiII c m a b) : PhiII c m b a := by
  have hm := T.hm
  obtain ⟨y₁, y₂, h1, h2, hne⟩ := T.exists_two_nbrs b
  obtain ⟨t₁, ⟨ht10, ht1m, ht1g, ht1y⟩, -⟩ := h.1 y₁ h1
  obtain ⟨t₂, ⟨ht20, ht2m, ht2g, ht2y⟩, -⟩ := h.1 y₂ h2
  have hnb : t₁ ∈ GPath.nbPaths c.graph a m :=
    ⟨ht10, GPath.noBack_of_dist_eq (CosetGeom.connected rfl) t₁ ht1g⟩
  have hrev : t₁.rev ∈ GPath.nbPaths c.graph b m := by
    refine ⟨?_, hnb.2.rev⟩
    rw [GPath.rev_apply _ (by omega), Nat.sub_zero, ht1m]
  have hrm : t₁.rev m = a := by
    rw [GPath.rev_apply _ le_rfl, Nat.sub_self, ht10]
  rcases T.alt hrev with ⟨-, hi⟩ | ⟨-, hii⟩
  · exfalso
    have e1 := hi t₁.rev (by rw [GPath.rev_apply _ (by omega), Nat.sub_zero, ht1m]) rfl ht1g.rev
    have e2 := hi t₂.rev (by rw [GPath.rev_apply _ (by omega), Nat.sub_zero, ht2m])
      (by rw [hrm, GPath.rev_apply _ le_rfl, Nat.sub_self, ht20]) ht2g.rev
    have e3 : t₁ = t₂ := by
      rw [← GPath.rev_rev t₁, e1, ← e2, GPath.rev_rev]
    apply hne
    rw [← ht1y, ← ht2y, e3]
  · rwa [hrm] at hii

end TransComp

namespace TransComp

variable {c} {m : ℕ} (T : TransComp c m)

include T

theorem geods_bij {a b : c.Γ} (h : PhiII c m a b) :
    Set.BijOn (fun t : GPath c.graph m => t 1) (c.geods m a b) (CosetGeom.nbrs a) := by
  have hm := T.hm
  have hs := T.phiII_symm h
  refine ⟨fun t ht => ?_, fun t₁ h₁ t₂ h₂ he => ?_, fun y hy => ?_⟩
  · show c.graph.Adj a (t 1)
    rw [← ht.1]
    exact t.adj 0 (by omega)
  · have e1 : t₁.rev (m - 1) = t₁ 1 := by
      rw [GPath.rev_apply _ (by omega)]; congr 1; omega
    have e2 : t₂.rev (m - 1) = t₂ 1 := by
      rw [GPath.rev_apply _ (by omega)]; congr 1; omega
    have hu := (hs.1 (t₁ 1) (by
      show c.graph.Adj a (t₁ 1)
      rw [← h₁.1]
      exact t₁.adj 0 (by omega))).unique
      (y₁ := t₁.rev) (y₂ := t₂.rev)
      ⟨by rw [GPath.rev_apply _ (by omega), Nat.sub_zero, h₁.2.1], by
        rw [GPath.rev_apply _ le_rfl, Nat.sub_self, h₁.1], h₁.2.2.rev, e1⟩
      ⟨by rw [GPath.rev_apply _ (by omega), Nat.sub_zero, h₂.2.1], by
        rw [GPath.rev_apply _ le_rfl, Nat.sub_self, h₂.1], h₂.2.2.rev, by rw [e2]; exact he.symm⟩
    rw [← GPath.rev_rev t₁, hu, GPath.rev_rev]
  · obtain ⟨t, ⟨ht0, htm, htg, hty⟩, -⟩ := hs.1 y hy
    refine ⟨t.rev, ⟨?_, ?_, htg.rev⟩, ?_⟩
    · rw [GPath.rev_apply _ (by omega), Nat.sub_zero, htm]
    · rw [GPath.rev_apply _ le_rfl, Nat.sub_self, ht0]
    · show t.rev 1 = y
      rw [GPath.rev_apply _ (by omega), ← hty]

theorem trans_nbrs {a b : c.Γ} (h : PhiII c m a b) {y z : c.Γ} (hy : c.graph.Adj a y)
    (hz : c.graph.Adj a z) : ∃ g : c.G0, g • a = a ∧ g • b = b ∧ g • y = z := by
  have hs := T.phiII_symm h
  obtain ⟨y', hy', hne⟩ : ∃ y', c.graph.Adj a y' ∧ y' ≠ y := by
    obtain ⟨w, hw, hwy, -⟩ := T.hval a y y
    exact ⟨w, hw, hwy⟩
  obtain ⟨z', hz', hne'⟩ : ∃ z', c.graph.Adj a z' ∧ z' ≠ z := by
    obtain ⟨w, hw, hwz, -⟩ := T.hval a z z
    exact ⟨w, hw, hwz⟩
  obtain ⟨g, hg1, hg2, hg3, -⟩ := hs.2.2 y y' z z' hy hy' hz hz' hne.symm hne'.symm
  exact ⟨g, hg2, hg1, hg3⟩

theorem stabPath_eq {a : c.Γ} {p : GPath c.graph m} (hp : p ∈ GPath.nbPaths c.graph a m) :
    (p.stabPath : Subgroup c.G0) = stv c a ⊓ stv c (p 1) ⊓ stv c (p m) := by
  have hm := T.hm
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hp.1]; exact h 0 (Nat.zero_le m)
    · exact h 1 hm
    · exact h m le_rfl
  · rintro ⟨⟨hga, hg1⟩, hgm⟩
    let t : GPath c.graph (m - 1) := p.drop 1 hm
    have ht0 : t ∈ GPath.nbPaths c.graph (p 1) (m - 1) :=
      ⟨by show p (1 + min 0 (m - 1)) = p 1; simp, hp.2.drop 1 hm⟩
    have htm : t (m - 1) = p m := by
      rw [GPath.drop_apply _ _ _ le_rfl]; congr 1; omega
    have hgt : g • t ∈ GPath.nbPaths c.graph (p 1) (m - 1) := by
      refine ⟨?_, GPath.smul_noBack ht0.2⟩
      show g • t 0 = p 1
      rw [ht0.1, hg1]
    have hgeo : (g • t).IsGeodesic := by
      show c.graph.dist ((g • t) 0) ((g • t) (m - 1)) = m - 1
      rw [hgt.1]
      exact T.dist_nbPath (by omega) hgt
    have heq := T.unique_geod (n := m - 1) (by omega) ht0 (q := g • t) hgt.1
      (by show g • t (m - 1) = t (m - 1); rw [htm, hgm]) hgeo
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [hp.1]; exact hga
    · have := congrArg (fun r : GPath c.graph (m - 1) => r (i - 1)) heq
      simp only [GPath.smul_apply] at this
      have e : t (i - 1) = p i := by
        rw [GPath.drop_apply _ _ _ (by omega)]; congr 1; omega
      rwa [e] at this

end TransComp

end RankTwoAmalgam.Completion

namespace LieSetting

variable {S : LieSetting.{u, w}}

theorem Facts45L.transComp (hS : S.Facts45L) : S.ι.TransComp S.m :=
  ⟨S.hι, hS.thick1, hS.thick2, hS.trans, by have := S.hm; omega⟩

theorem Facts45L.compl_path (hS : S.Facts45L) {u : S.ι.Γ} {p : GPath S.ι.graph S.m}
    (hp : p ∈ GPath.nbPaths S.ι.graph u S.m) :
    IsComplementIn p.stabPath (S.Qbar u) (stv S.ι u ⊓ stv S.ι (p 1)) := by
  have T := hS.transComp
  have hm := S.hm
  have hd : S.ι.graph.dist u (p S.m) = S.m := T.dist_nbPath le_rfl hp
  have h1 := hS.compl u (p S.m) hd
  have hadj : S.ι.graph.Adj u (p 1) := by
    rw [← hp.1]; exact p.adj 0 (by omega)
  have hQ : S.Qbar u ≤ stv S.ι u ⊓ stv S.ι (p 1) :=
    le_inf (S.Qbar_le_stv u) (hS.Qle u (p 1) hadj)
  have h2 := h1.inf_left hQ inf_le_left
  have e : (p.stabPath : Subgroup S.ι.G0) =
      (stv S.ι u ⊓ stv S.ι (p S.m)) ⊓ (stv S.ι u ⊓ stv S.ι (p 1)) := by
    rw [T.stabPath_eq hp]
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [e]
  exact h2

end LieSetting

namespace LieSetting

variable {S : LieSetting.{u, w}} {Y : Type w'} [Group Y] [Finite Y]

omit [Finite Y] in
theorem Facts45L.complement_x (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    {p : GPath β.graph S.m} (hp : p ∈ GPath.nbPaths β.graph β.xv S.m) :
    IsComplementIn p.stabPath (S.Qx β) (stv β β.xv ⊓ stv β (p 1)) := by
  have hm := S.hm
  obtain ⟨ph, ⟨hph0, hphp⟩, -⟩ := (β.graphCovering hβ).lift_path xhat S.m p
    (by rw [hp.1]; exact (Θ_xhat β hβ).symm)
  have hpb0 : (S.ι.graphCovering S.hι).pathMap ph ∈ GPath.nbPaths S.ι.graph S.ι.xv S.m := by
    refine ⟨?_, ?_⟩
    · show S.ι.Θ S.hι (ph 0) = S.ι.xv
      rw [hph0]; exact Θ_xhat S.ι S.hι
    · rw [(S.ι.graphCovering S.hι).noBack_pathMap_iff,
        ← (β.graphCovering hβ).noBack_pathMap_iff, hphp]
      exact hp.2
  have h1 := hS.compl_path hpb0
  have rg : stv S.ι S.ι.xv ≤ (f1 (c := S.ι)).range := stv_xv_le_range_f1 S.ι
  have h2 := (IsComplementIn.comap_iff (f1 (c := S.ι)) (f1_injective S.ι S.hι)
    ((GPath.stabPath_le_stabilizer _ hpb0.1).trans rg) ((S.Qbar_le_stv _).trans rg)
    (inf_le_left.trans rg)).mp h1
  have e1 : ((S.ι.graphCovering S.hι).pathMap ph).stabPath.comap (f1 (c := S.ι)) =
      S.α.gam1 ph := comap_f1_stabPath S.ι S.hι ph hph0
  have e3 := comap_f1_stv_inf S.ι S.hι ph hph0 (by omega : 1 ≤ S.m)
  have e2 : (S.Qbar S.ι.xv).comap (f1 (c := S.ι)) = S.Qb1 := rfl
  rw [e1, e2, e3] at h2
  have rgβ : stv β β.xv ≤ (f1 (c := β)).range := stv_xv_le_range_f1 β
  have hp1 : p.stabPath ≤ stv β β.xv := GPath.stabPath_le_stabilizer p hp.1
  have e1β : p.stabPath.comap (f1 (c := β)) = S.α.gam1 ph := by
    rw [← hphp]; exact comap_f1_stabPath β hβ ph hph0
  have e2β : (S.Qx β).comap (f1 (c := β)) = S.Qb1 :=
    Subgroup.comap_map_eq_self_of_injective (f1_injective β hβ) _
  have e3β : (stv β β.xv ⊓ stv β (p 1)).comap (f1 (c := β)) = S.α.gam1 (ph.take 1 (by omega)) := by
    rw [← hphp]; exact comap_f1_stv_inf β hβ ph hph0 (by omega : 1 ≤ S.m)
  have hQβ : S.Qx β ≤ (f1 (c := β)).range := Subgroup.map_le_range _ _
  rw [IsComplementIn.comap_iff (f1 (c := β)) (f1_injective β hβ) (hp1.trans rgβ)
    hQβ (inf_le_left.trans rgβ), e1β, e2β, e3β]
  exact h2

omit [Finite Y] in
theorem Facts45L.complement_l (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    {p : GPath β.graph S.m} (hp : p ∈ GPath.nbPaths β.graph β.lv S.m) :
    IsComplementIn p.stabPath (S.Ql β) (stv β β.lv ⊓ stv β (p 1)) := by
  have hm := S.hm
  obtain ⟨ph, ⟨hph0, hphp⟩, -⟩ := (β.graphCovering hβ).lift_path lhat S.m p
    (by rw [hp.1]; exact (Θ_lhat β hβ).symm)
  have hpb0 : (S.ι.graphCovering S.hι).pathMap ph ∈ GPath.nbPaths S.ι.graph S.ι.lv S.m := by
    refine ⟨?_, ?_⟩
    · show S.ι.Θ S.hι (ph 0) = S.ι.lv
      rw [hph0]; exact Θ_lhat S.ι S.hι
    · rw [(S.ι.graphCovering S.hι).noBack_pathMap_iff,
        ← (β.graphCovering hβ).noBack_pathMap_iff, hphp]
      exact hp.2
  have h1 := hS.compl_path hpb0
  have rg : stv S.ι S.ι.lv ≤ (f2 (c := S.ι)).range := stv_lv_le_range_f2 S.ι
  have h2 := (IsComplementIn.comap_iff (f2 (c := S.ι)) (f2_injective S.ι S.hι)
    ((GPath.stabPath_le_stabilizer _ hpb0.1).trans rg) ((S.Qbar_le_stv _).trans rg)
    (inf_le_left.trans rg)).mp h1
  have e1 : ((S.ι.graphCovering S.hι).pathMap ph).stabPath.comap (f2 (c := S.ι)) =
      S.α.gam2 ph := comap_f2_stabPath S.ι S.hι ph hph0
  have e3 := comap_f2_stv_inf S.ι S.hι ph hph0 (by omega : 1 ≤ S.m)
  have e2 : (S.Qbar S.ι.lv).comap (f2 (c := S.ι)) = S.Qb2 := rfl
  rw [e1, e2, e3] at h2
  have rgβ : stv β β.lv ≤ (f2 (c := β)).range := stv_lv_le_range_f2 β
  have hp1 : p.stabPath ≤ stv β β.lv := GPath.stabPath_le_stabilizer p hp.1
  have e1β : p.stabPath.comap (f2 (c := β)) = S.α.gam2 ph := by
    rw [← hphp]; exact comap_f2_stabPath β hβ ph hph0
  have e2β : (S.Ql β).comap (f2 (c := β)) = S.Qb2 :=
    Subgroup.comap_map_eq_self_of_injective (f2_injective β hβ) _
  have e3β : (stv β β.lv ⊓ stv β (p 1)).comap (f2 (c := β)) = S.α.gam2 (ph.take 1 (by omega)) := by
    rw [← hphp]; exact comap_f2_stv_inf β hβ ph hph0 (by omega : 1 ≤ S.m)
  have hQβ : S.Ql β ≤ (f2 (c := β)).range := Subgroup.map_le_range _ _
  rw [IsComplementIn.comap_iff (f2 (c := β)) (f2_injective β hβ) (hp1.trans rgβ)
    hQβ (inf_le_left.trans rgβ), e1β, e2β, e3β]
  exact h2

omit [Finite Y] in
theorem Facts45L.complement (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    (a : β.Γ) {p : GPath β.graph S.m} (hp : p ∈ GPath.nbPaths β.graph a S.m) :
    IsComplementIn p.stabPath (β.Qvert (S.Qx β) (S.Ql β) a) (stv β a ⊓ stv β (p 1)) := by
  have hQ := S.Qx_normalized β
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert β a
  have hq : g⁻¹ • p ∈ GPath.nbPaths β.graph (β.baseVert (CosetGeom.vtype a)) S.m := by
    refine ⟨?_, GPath.smul_noBack hp.2⟩
    show g⁻¹ • p 0 = _
    rw [hp.1]
    exact inv_smul_eq_iff.mpr hg.symm
  have key : ∀ (b : Bool) (q : GPath β.graph S.m), q ∈ GPath.nbPaths β.graph (β.baseVert b) S.m →
      IsComplementIn q.stabPath (cond b (S.Ql β) (S.Qx β)) (stv β (β.baseVert b) ⊓ stv β (q 1)) := by
    intro b q hq
    cases b
    · exact hS.complement_x β hβ hq
    · exact hS.complement_l β hβ hq
  have h2 := (IsComplementIn.conjSub_iff g).mpr (key _ _ hq)
  have e1 : conjSub g (g⁻¹ • p).stabPath = p.stabPath := by
    rw [← GPath.stabPath_smul, ← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  have e3 : conjSub g (stv β (β.baseVert (CosetGeom.vtype a)) ⊓ stv β ((g⁻¹ • p) 1)) =
      stv β a ⊓ stv β (p 1) := by
    rw [conjSub_inf, ← stv_smul, ← stv_smul, hg, GPath.smul_apply, smul_inv_smul]
  rw [e1, e3, ← Qvert_eq_conjSub hQ hg] at h2
  exact h2

theorem Facts45L.lemma_F46_8 (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    (a : β.Γ) {p : GPath β.graph S.m} (hp : p ∈ GPath.nbPaths β.graph a S.m) :
    β.graph.dist a (p S.m) = S.m ∧
    ((∀ t : GPath β.graph S.m, t 0 = a → t S.m = p S.m → t.IsGeodesic → t = p) ∨
      (IsComplementIn (stv β a ⊓ stv β (p S.m)) (β.Qvert (S.Qx β) (S.Ql β) a) (stv β a) ∧
        (∀ t₁ t₂ t₃ t₄ : GPath β.graph S.m, t₁ ∈ β.geods S.m a (p S.m) →
          t₂ ∈ β.geods S.m a (p S.m) → t₃ ∈ β.geods S.m a (p S.m) → t₄ ∈ β.geods S.m a (p S.m) →
          t₁ ≠ t₂ → t₃ ≠ t₄ → ∃ g : β.G0, g • a = a ∧ g • p S.m = p S.m ∧ g • t₁ = t₃ ∧
            g • t₂ = t₄) ∧
        Set.BijOn (fun t : GPath β.graph S.m => t 1) (β.geods S.m a (p S.m))
          (CosetGeom.nbrs a))) := by
  have hm := S.hm
  have T : β.TransComp S.m :=
    ⟨hβ, hS.thick1, hS.thick2, pathTrans_transfer β hβ S.ι S.hι (S.m + 1) hS.trans, by omega⟩
  refine ⟨T.dist_nbPath le_rfl hp, ?_⟩
  rcases T.alt hp with ⟨-, hi⟩ | ⟨-, hii⟩
  · exact Or.inl hi
  right
  have hQ := S.Qx_normalized β
  have hc := hS.complement β hβ a hp
  refine ⟨⟨hc.1.trans inf_le_left, inf_le_left, ?_, ?_⟩, hii.2.1, T.geods_bij hii⟩
  · refine eq_bot_iff.mpr fun x hx => ?_
    have hx1 := hc.1 hx.1
    have hx2 : x ∈ p.stabPath := by
      rw [T.stabPath_eq hp]
      exact ⟨hx1, hx.2.2⟩
    have : x ∈ β.Qvert (S.Qx β) (S.Ql β) a ⊓ p.stabPath := ⟨hx.1, hx2⟩
    rw [hc.2.2.1] at this
    exact this
  · intro g hg
    have hga : g • a = a := MulAction.mem_stabilizer_iff.mp hg
    have hadj : β.graph.Adj a (p 1) := by
      rw [← hp.1]; exact p.adj 0 (by omega)
    have hadj' : β.graph.Adj a (g • p 1) := by
      have := (GraphAction.adj_smul g a (p 1)).mpr hadj
      rwa [hga] at this
    obtain ⟨h, hha, hhb, hhy⟩ := T.trans_nbrs hii hadj hadj'
    have hmem : h⁻¹ * g ∈ stv β a ⊓ stv β (p 1) := by
      refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
      · rw [mul_smul, hga, inv_smul_eq_iff]; exact hha.symm
      · rw [mul_smul, ← hhy, inv_smul_smul]
    obtain ⟨q, hq, k, hk, hqk⟩ := hc.2.2.2 _ hmem
    have hkab : k ∈ stv β a ⊓ stv β (p S.m) := by
      rw [T.stabPath_eq hp] at hk
      exact ⟨hk.1.1, hk.2⟩
    have hhK : h ∈ stv β a ⊓ stv β (p S.m) :=
      ⟨MulAction.mem_stabilizer_iff.mpr hha, MulAction.mem_stabilizer_iff.mpr hhb⟩
    have hconj : conjSub h (β.Qvert (S.Qx β) (S.Ql β) a) = β.Qvert (S.Qx β) (S.Ql β) a := by
      rw [← Qvert_smul hQ h a, hha]
    refine ⟨h * q * h⁻¹, ?_, h * k, (stv β a ⊓ stv β (p S.m)).mul_mem hhK hkab, ?_⟩
    · rw [← hconj]; exact mul_mem_conjSub hq
    · calc h * q * h⁻¹ * (h * k) = h * (q * k) := by group
        _ = g := by rw [hqk]; group

end LieSetting

end CFSG.Quasithin

