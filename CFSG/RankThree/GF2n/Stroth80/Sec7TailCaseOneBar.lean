module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z0Data
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.yCKN (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hNK : bar M Q (hc.CN t) ≤ bar M Q (NormH0 M Z Z0))
    (hKH : bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z)) :
    ∀ k ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      (∀ n ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), k * n = n * k) →
      k ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
  intro k hk hkc
  have hkK : (k : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) := Subgroup.mem_subgroupOf.mp hk
  have hcent : (⟨(k : Mbar M Q), hkK⟩ : bar M Q (NormH0 M Z Z0)) ∈
      Subgroup.centralizer (generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) :
        Set ↥(bar M Q (NormH0 M Z Z0))) := by
    rw [hF, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : Mbar M Q) ∈ bar M Q (hc.CN t) := Subgroup.mem_subgroupOf.mp hy
    have hyH : (y : Mbar M Q) ∈ bar M Q (H0 M Z) := hKH y.2
    have hn : (⟨(y : Mbar M Q), hyH⟩ : bar M Q (H0 M Z)) ∈
        (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) :=
      Subgroup.mem_subgroupOf.mpr hy'
    have h := congrArg Subtype.val (hkc _ hn)
    exact Subtype.ext (by simpa using h.symm)
  have h2 := CFSG.centralizer_generalizedFitting_le _ hcent
  rw [hF] at h2
  exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h2)

theorem exists_sylow_le_of_max_transfer {Y : Type} [Group Y] {K H : Subgroup Y} (hKH : K ≤ H)
    (hmax : ∀ S : Subgroup Y, S ≤ K → IsPGroup 2 S →
      (∀ T : Subgroup Y, T ≤ K → IsPGroup 2 T → S ≤ T → T = S) →
      ∀ T : Subgroup Y, T ≤ H → IsPGroup 2 T → S ≤ T → T = S) :
    ∃ P : Sylow 2 ↥H, (P : Subgroup ↥H) ≤ K.subgroupOf H := by
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥K) := Sylow.nonempty
  obtain ⟨S, hS⟩ : ∃ S : Subgroup Y, S = (P₀ : Subgroup ↥K).map K.subtype := ⟨_, rfl⟩
  have hSK : S ≤ K := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hSp : IsPGroup 2 S := by
    rw [hS]
    exact P₀.isPGroup'.map K.subtype
  have hSmax : ∀ T : Subgroup Y, T ≤ K → IsPGroup 2 T → S ≤ T → T = S := by
    intro T hTK hTp hST
    have hPT : (P₀ : Subgroup ↥K) ≤ T.subgroupOf K := by
      intro x hx
      have hxS : (x : Y) ∈ S := by
        rw [hS]
        exact Subgroup.mem_map_of_mem K.subtype hx
      exact hST hxS
    have hTp' : IsPGroup 2 (T.subgroupOf K) := hTp.comap_subtype
    have heq : T.subgroupOf K = (P₀ : Subgroup ↥K) := P₀.is_maximal' hTp' hPT
    calc T = (T.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hTK).symm
      _ = (P₀ : Subgroup ↥K).map K.subtype := by rw [heq]
      _ = S := hS.symm
  refine ⟨{ toSubgroup := S.subgroupOf H, isPGroup' := hSp.comap_subtype, is_maximal' := ?_ },
    Subgroup.subgroupOf_mono H hSK⟩
  intro T hT hST
  have hT1 : T.map H.subtype ≤ H := Subgroup.map_subtype_le T
  have hT1p : IsPGroup 2 (T.map H.subtype) := hT.map H.subtype
  have hST1 : S ≤ T.map H.subtype := by
    intro x hx
    have hxH : x ∈ H := hKH (hSK hx)
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ S.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map_of_mem H.subtype (hST hmem)
  have hTS : T.map H.subtype = S := hmax S hSK hSp hSmax (T.map H.subtype) hT1 hT1p hST1
  have hTeq : T = (T.map H.subtype).subgroupOf H :=
    (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H) T).symm
  calc T = (T.map H.subtype).subgroupOf H := hTeq
    _ = S.subgroupOf H := by rw [hTS]

theorem Ctx.ySylow (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t)))
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hC : CentTwoInV hc t Z0) :
    ∃ S : Sylow 2 ↥(bar M Q (H0 M Z)),
      (S : Subgroup ↥(bar M Q (H0 M Z))) ≤
        (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)) := by
  have hKH : bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z) :=
    bar_mono' (fun x hx => (Subgroup.mem_inf.mp hx).1)
  exact exists_sylow_le_of_max_transfer hKH
    (fun S hSK hSp hS T hT hTp hST =>
      hc.sylow_of_cent2 hs hZ0 hZt hZcard hN2 hTI hC hSK hSp hS T hT hTp hST)

theorem conjSubgroup_le_of_mem_yConj {X : Type} [Group X] {H S : Subgroup X} {g : X}
    (hg : g ∈ H) (hS : S ≤ H) : conjSubgroup g S ≤ H := by
  intro y hy
  have hz : g⁻¹ * y * g ∈ S := mem_conjSubgroup.mp hy
  have h := H.mul_mem (H.mul_mem hg (hS hz)) (H.inv_mem hg)
  have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rwa [e] at h

theorem mem_conjSubgroup_subgroupOf_yConj {X : Type} [Group X] {H T : Subgroup X} (g x : H) :
    x ∈ conjSubgroup g (T.subgroupOf H) ↔ (x : X) ∈ conjSubgroup (g : X) T := by
  rw [mem_conjSubgroup, mem_conjSubgroup, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem Ctx.yConj (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hcase1 : ∀ g ∈ M, conjSubgroup g Z0 ≤ NormH0 M Z Z0 → conjSubgroup g Z0 ≤ hc.CN t) :
    ∀ g : ↥(bar M Q (H0 M Z)),
      conjSubgroup g ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ≤
        (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)) →
      conjSubgroup g ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ≤
        (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
  intro g hg
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hQK : Q ≤ NormH0 M Z Z0 := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hQH hq, Subgroup.le_normalizer (hQZ0 hq)⟩
  obtain ⟨gb, hgb⟩ := g
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) gb
  have hg₀H : (g₀ : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH g₀).mp hgb
  have step1 : conjSubgroup (g₀ : G) Z0 ≤ NormH0 M Z Z0 := by
    intro y hy
    have hyM : y ∈ M := conjSubgroup_le_of_mem_yConj g₀.2 hZ0M hy
    have hyH : y ∈ H0 M Z := conjSubgroup_le_of_mem_yConj hg₀H hZ0H0 hy
    have hw : QuotientGroup.mk' (Q.subgroupOf M) (⟨y, hyM⟩ : ↥M) ∈ bar M Q (H0 M Z) :=
      (mk_mem_bar_iff_sec4 hQH ⟨y, hyM⟩).mpr hyH
    have hwV : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩, hw⟩ : ↥(bar M Q (H0 M Z))) ∈
        conjSubgroup ⟨QuotientGroup.mk' (Q.subgroupOf M) g₀, hgb⟩
          ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
      rw [mem_conjSubgroup_subgroupOf_yConj]
      exact (mk_mem_conj_bar_iff_sec4 hQZ0 g₀ ⟨y, hyM⟩).mpr hy
    have hwK := Subgroup.mem_subgroupOf.mp (hg hwV)
    exact (mk_mem_bar_iff_sec4 hQK ⟨y, hyM⟩).mp hwK
  have step2 : conjSubgroup (g₀ : G) Z0 ≤ hc.CN t := hcase1 (g₀ : G) g₀.2 step1
  intro x hx
  obtain ⟨xb, hxb⟩ := x
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) xb
  have hx' := (mem_conjSubgroup_subgroupOf_yConj _ _).mp hx
  have hx₀ : (x₀ : G) ∈ conjSubgroup (g₀ : G) Z0 :=
    (mk_mem_conj_bar_iff_sec4 hQZ0 g₀ x₀).mp hx'
  exact Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.mem_subgroupOf.mpr (step2 hx₀)))

theorem Ctx.yComm (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hCN : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0)
    (hNH : bar M Q (hc.CN t) ≤ bar M Q (H0 M Z)) :
    ⁅(bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))⁆ ≤
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
  have hcomm : ((⁅x, y⁆ : ↥(bar M Q (H0 M Z))) : Mbar M Q) =
      QuotientGroup.mk' (Q.subgroupOf M) ⁅s, r⁆ := by
    simp only [map_commutatorElement, commutatorElement_def, Subgroup.coe_mul,
      Subgroup.coe_inv, map_mul, map_inv, hsx, hry]
  have hsr : ((⁅s, r⁆ : ↥M) : G) = ⁅(s : G), (r : G)⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  have hmem : (⁅s, r⁆ : ↥M) ∈ Z0.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf, hsr]
    exact hCN _ (Subgroup.mem_subgroupOf.mp hs) _ (Subgroup.mem_subgroupOf.mp hr)
  rw [Subgroup.mem_subgroupOf, hcomm]
  exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (Q.subgroupOf M)) hmem

theorem wac_commutator_le {Y : Type} [Group Y] {V N : Subgroup Y}
    (hconj : ∀ g : Y, conjSubgroup g V ≤ Subgroup.normalizer (V : Set Y) → conjSubgroup g V ≤ N)
    (hNc : ⁅N, N⁆ ≤ V) : ⁅WAC V, WAC V⁆ ≤ V := by
  have hWN : WAC V ≤ N := by
    unfold WAC
    exact iSup_le fun g => iSup_le fun hg =>
      hconj g (hg.trans (Subgroup.centralizer_le_normalizer _))
  exact (Subgroup.commutator_mono hWN hWN).trans hNc

theorem Ctx.ySq (h51 : Stroth51Statement) (hA : Sec7AExistsStatement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {L : Subgroup G}
    (hL : Sec717L hc t Z0 L) :
    ∀ x ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
      x * x ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
  intro x hx
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hsq : ∀ y ∈ hc.CN t, y ^ 2 ∈ Z0 := hopp.2.2.2.2.2.2.2.1
  have hQL : Q ≤ L := hL.1
  have hLN : L ≤ hc.CN t := hL.2.1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs.toSec5.mem hZ0
  have hxL : (x : ↥M ⧸ Q.subgroupOf M) ∈ bar M Q L := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : ↥M ⧸ Q.subgroupOf M)
  rw [← hy] at hxL
  have hyL : (y : G) ∈ L := (mk_mem_bar_iff_sec4 hQL y).mp hxL
  have hyy : (y : G) * (y : G) ∈ Z0 := by
    have h2 := hsq _ (hLN hyL)
    rwa [pow_two] at h2
  apply Subgroup.mem_subgroupOf.mpr
  have hxx : ((x * x : ↥(bar M Q (H0 M Z))) : ↥M ⧸ Q.subgroupOf M) =
      QuotientGroup.mk' (Q.subgroupOf M) (y * y) := by
    rw [Subgroup.coe_mul, ← hy, map_mul]
  rw [hxx]
  exact (mk_mem_bar_iff_sec4 hQZ0 (y * y)).mpr (by rw [Subgroup.coe_mul]; exact hyy)

end CFSG.RankThree.GF2n.Stroth80
