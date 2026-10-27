module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5StdSub
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneHyperplane

public section

namespace CFSG.StandardType.FrameRoute.TwE6Model

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def planeF {G : Type} [Group G] {Bs : Subgroup G}
    (z : G) (u : G → NTPlane.X3)
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu1 : u 1 = 0) : Subgroup G where
  carrier := {b | b ∈ Bs ∧ ∃ c : ZMod 3, u b = c • u z}
  one_mem' := by
    refine ⟨Subgroup.one_mem Bs, 0, ?_⟩
    rw [hu1, zero_smul]
  mul_mem' := by
    rintro b b' ⟨hb, c, hc⟩ ⟨hb', c', hc'⟩
    exact ⟨Bs.mul_mem hb hb', c + c', by rw [hadd b hb b' hb', hc, hc', add_smul]⟩
  inv_mem' := by
    rintro b ⟨hb, c, hc⟩
    have hinv : u b⁻¹ = -u b := by
      have h := hadd b hb b⁻¹ (Bs.inv_mem hb)
      rw [mul_inv_cancel, hu1] at h
      exact eq_neg_of_add_eq_zero_right h.symm
    exact ⟨Bs.inv_mem hb, -c, by rw [hinv, hc, neg_smul]⟩

private theorem planeF_u_pow {G : Type} [Group G] {Bs : Subgroup G} {z : G}
    {u : G → NTPlane.X3} (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu1 : u 1 = 0) (hz : z ∈ Bs) (k : ℕ) : u (z ^ k) = k • u z := by
  induction k with
  | zero => rw [pow_zero, hu1, zero_smul]
  | succ k ih =>
    rw [pow_succ, hadd (z ^ k) (Bs.pow_mem hz k) z hz, ih, succ_nsmul]

private theorem planeF_inf_eq_closure {G : Type} [Group G] {B Bs : Subgroup G} {x z : G}
    {u : G → NTPlane.X3} (hBBs : B ≤ Bs) (hxB : x ∈ B) (hzB : z ∈ B)
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x) (hu1 : u 1 = 0) :
    B ⊓ planeF z u hadd hu1 = Subgroup.closure {x, z} := by
  have hzBs : z ∈ Bs := hBBs hzB
  have hxBs : x ∈ Bs := hBBs hxB
  have hx0 : u x = 0 := (hu0 x hxBs).mpr (Subgroup.mem_zpowers x)
  refine le_antisymm ?_ ?_
  · intro b hb
    rw [Subgroup.mem_inf] at hb
    obtain ⟨hbB, hbF⟩ := hb
    obtain ⟨hbBs, c, hc⟩ := hbF
    have hzpow : u (z ^ c.val) = c • u z := by
      rw [planeF_u_pow hadd hu1 hzBs c.val,
        ← Nat.cast_smul_eq_nsmul (R := ZMod 3) c.val (u z), ZMod.natCast_zmod_val]
    have hinv : u ((z ^ c.val)⁻¹) = -(c • u z) := by
      have h := hadd (z ^ c.val) (Bs.pow_mem hzBs c.val) ((z ^ c.val))⁻¹
        (Bs.inv_mem (Bs.pow_mem hzBs c.val))
      rw [mul_inv_cancel, hu1] at h
      rw [eq_neg_of_add_eq_zero_right h.symm, hzpow]
    have hkey : u (b * (z ^ c.val)⁻¹) = 0 := by
      rw [hadd b hbBs ((z ^ c.val))⁻¹ (Bs.inv_mem (Bs.pow_mem hzBs c.val)), hc, hinv]
      abel
    have hmem : b * (z ^ c.val)⁻¹ ∈ Subgroup.zpowers x :=
      (hu0 (b * (z ^ c.val)⁻¹)
        (Bs.mul_mem hbBs (Bs.inv_mem (Bs.pow_mem hzBs c.val)))).mp hkey
    have hxcl : x ∈ Subgroup.closure ({x, z} : Set G) := Subgroup.subset_closure (by simp)
    have hzcl : z ∈ Subgroup.closure ({x, z} : Set G) := Subgroup.subset_closure (by simp)
    have h1 : b * (z ^ c.val)⁻¹ ∈ Subgroup.closure ({x, z} : Set G) :=
      Subgroup.zpowers_le.mpr hxcl hmem
    have h2 : z ^ c.val ∈ Subgroup.closure ({x, z} : Set G) := Subgroup.pow_mem _ hzcl _
    have heq : b = (b * (z ^ c.val)⁻¹) * z ^ c.val := by group
    rw [heq]
    exact Subgroup.mul_mem _ h1 h2
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y (rfl | rfl)
    · exact Subgroup.mem_inf.mpr ⟨hxB, hxBs, 0, by rw [hx0, zero_smul]⟩
    · exact Subgroup.mem_inf.mpr ⟨hzB, hzBs, 1, by rw [one_smul]⟩

private def twE6Hom {G : Type} [Group G] {B Bs : Subgroup G} {u : G → NTPlane.X3}
    (hBBs : B ≤ Bs) (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b') :
    ↥B →* Multiplicative NTPlane.X3 :=
  MonoidHom.mk' (fun b => Multiplicative.ofAdd (u b)) fun b b' => by
    change Multiplicative.ofAdd (u (b * b')) =
      Multiplicative.ofAdd (u b) * Multiplicative.ofAdd (u b')
    rw [hadd (b : G) (hBBs b.2) (b' : G) (hBBs b'.2), ofAdd_add]

private theorem twE6_image_card {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {u : G → NTPlane.X3} (hBBs : B ≤ Bs) (hxB : x ∈ B) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x) :
    Nat.card B = 3 * Nat.card (Subgroup.toAddSubgroup' (twE6Hom hBBs hadd).range) := by
  let f := twE6Hom hBBs hadd
  let H := Subgroup.toAddSubgroup' f.range
  have hker : f.ker.map B.subtype = Subgroup.zpowers x := by
    ext b
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp ha)
      exact (hu0 (a : G) (hBBs a.2)).mp (by simpa [f, twE6Hom] using h)
    · intro hb
      have hbB : b ∈ B := Subgroup.zpowers_le.mpr hxB hb
      refine ⟨⟨b, hbB⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      change Multiplicative.ofAdd (u b) = 1
      rw [(hu0 b (hBBs hbB)).mpr hb]
      rfl
  have hcardker : Nat.card f.ker = 3 := by
    have h := Subgroup.card_map_of_injective (K := f.ker) B.subtype_injective
    rw [hker, Nat.card_zpowers, orderOf_eq_prime hx3 hx1] at h
    exact h.symm
  have hBcard : Nat.card B = Nat.card f.range * 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [show Nat.card (↥B ⧸ f.ker) = Nat.card f.range from
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hcardker] at h
    exact h
  have hHcard : Nat.card H = Nat.card f.range := by
    change Nat.card ↥(Subgroup.toAddSubgroup' f.range) = Nat.card ↥f.range
    refine Nat.card_congr ⟨fun v => ⟨Multiplicative.ofAdd v.1, ?_⟩,
      fun w => ⟨Multiplicative.toAdd w.1, ?_⟩, fun v => Subtype.ext (by simp),
      fun w => Subtype.ext (by simp)⟩
    · exact (Subgroup.mem_toAddSubgroup' f.range v.1).mp v.2
    · exact (Subgroup.mem_toAddSubgroup' f.range _).mpr (by simp)
  rw [hBcard, hHcard, Nat.mul_comm]

private theorem twE6_image_five {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {u : G → NTPlane.X3}
    (hBBs : B ≤ Bs) (hxB : x ∈ B) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x)
    (hcardB : 3 ^ 6 ≤ Nat.card B) :
    ∃ H : AddSubgroup NTPlane.X3, 3 ^ 5 ≤ Nat.card H ∧
      ∀ v ∈ H, ∃ b ∈ B, u b = v := by
  let f := twE6Hom hBBs hadd
  let H := Subgroup.toAddSubgroup' f.range
  have hBcard : Nat.card B = 3 * Nat.card H := twE6_image_card hBBs hxB hx1 hx3 hadd hu0
  have h1 : (3 : ℕ) * 3 ^ 5 ≤ 3 * Nat.card H := by
    rw [← hBcard]
    simpa [show (3 : ℕ) ^ 6 = 3 * 3 ^ 5 from by norm_num] using hcardB
  refine ⟨H, Nat.le_of_mul_le_mul_left h1 (by norm_num), ?_⟩
  intro v hv
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ((Subgroup.mem_toAddSubgroup' f.range v).mp hv)
  exact ⟨b.1, b.2, by simpa [f, twE6Hom] using congrArg Multiplicative.toAdd hb⟩

theorem exists_point_typeA5 {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {u : G → NTPlane.X3}
    (hBBs : B ≤ Bs) (hxB : x ∈ B) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x)
    (hcardB : 3 ^ 6 ≤ Nat.card B) :
    ∃ z ∈ B, (NTPlane.kerRoots (u z)).ncard = 30 ∧ z ∉ Subgroup.zpowers x := by
  obtain ⟨H, hHcard, hH⟩ := twE6_image_five hBBs hxB hx1 hx3 hadd hu0 hcardB
  obtain ⟨v, hvH, hv30⟩ := NTPlane.exists_mem_ncard_kerRoots_eq_thirty H hHcard
  obtain ⟨b, hbB, hbu⟩ := hH v hvH
  refine ⟨b, hbB, ?_, ?_⟩
  · rw [hbu]
    exact hv30
  · intro hb
    have h0 : u b = 0 := (hu0 b (hBBs hbB)).mpr hb
    have hv0 : v = 0 := by rw [← hbu]; exact h0
    have h72 : (NTPlane.kerRoots v).ncard = 72 := by rw [hv0]; exact NTPlane.ncard_kerRoots_zero
    omega

private theorem twE6_goodPlane_component {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x z : G} {L : Subgroup G} {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {u : G → NTPlane.X3} {φ : NTPlane.X3 → MulAut R}
    {J : Subgroup R} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x)
    (hzB : z ∈ B) (hznot : z ∉ Subgroup.zpowers x) (hB9 : 9 < Nat.card B)
    {lab₀ : LargeEvenLabel} {r : ℕ}
    (hJq : CFSG.IsQuasisimple ↥J)
    (hJfix : J ≤ TauCeti.fixedSubgroup (φ (u z)).toMonoidHom)
    (hJnorm : (J.subgroupOf (TauCeti.fixedSubgroup (φ (u z)).toMonoidHom)).Normal)
    (hJsolv : IsSolvable (↥(TauCeti.fixedSubgroup (φ (u z)).toMonoidHom) ⧸
      J.subgroupOf (TauCeti.fixedSubgroup (φ (u z)).toMonoidHom)))
    (hJbig : 25920 < Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJmark : LargeEvenMarking ↥J (fun lab _ _ _ _ _ => lab = lab₀))
    (hJdet : ∀ w : NTPlane.X3, (∀ j ∈ J, φ w j = j) ↔ ∃ c : ZMod 3, w = c • u z)
    (hJcov : ∀ (J₁ : Type) [Group J₁] [Finite J₁] (π : J₁ →* ↥J), Function.Surjective π →
      π.ker ≤ Subgroup.center J₁ → Rank3Witness J₁ r)
    (hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) (φ (u z)))
    (hψ : ∀ b ∈ Bs, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (φ (u b))) :
    ∃ (F J₁ : Subgroup G),
      LargeEvenStdSub 3 B x L (Subgroup.closure {x, z}) J₁ ∧
      Bs ⊓ Subgroup.centralizer (J₁ : Set G) = F ∧
      B ⊓ F = Subgroup.closure {x, z} ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = lab₀) ∧
      Rank3Witness ↥J₁ r ∧ Subgroup.closure {x, z} ≠ B := by
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  obtain ⟨hDB, hDe, hDc, hDB'⟩ := closure_pair_facts hS.1.1 hS.2.1 hS.2.2.1 hzB hznot hB9
  have hx : x ∈ Subgroup.centralizer (L : Set G) :=
    (Subgroup.mem_inf.mp (hker ▸ Subgroup.mem_zpowers x)).2
  have hzN : z ∈ Subgroup.normalizer (L : Set G) := hN (hBs.1 hzB)
  have hu1 : u 1 = 0 := (hu0 1 (Subgroup.one_mem Bs)).mpr (Subgroup.one_mem _)
  have hFdet : ∀ b, b ∈ planeF z u hadd hu1 ↔ b ∈ Bs ∧ ∀ j ∈ J, φ (u b) j = j :=
    fun b => ⟨fun hb => ⟨hb.1, (hJdet (u b)).mpr hb.2⟩,
      fun hb => ⟨hb.1, (hJdet (u b)).mp hb.2⟩⟩
  have hBF : B ⊓ planeF z u hadd hu1 = Subgroup.closure {x, z} :=
    planeF_inf_eq_closure hBs.1 hS.2.1 hzB hadd hu0 hu1
  have hcc := @coverComponent_eq_layer G _ L _ _ θ x z (φ (u z)) J hx hzN hφ hJq hJfix hJnorm hJsolv
  obtain ⟨J₁, hlay, -, -, -, -, hmark, hcent, hstd⟩ :=
    @exists_goodPlane_component_of_cover G _ L _ _ θ B Bs (planeF z u hadd hu1) x z
      (φ (u z)) J hDB hDe hDc hx hzN hφ hJq hJfix hJnorm hJsolv hJbig lab₀ hJmark
      hBs.1 hN (fun b => φ (u b)) hψ hFdet hBF
  have hcov : Rank3Witness ↥(coverComponent θ J) r := rank3Witness_coverComponent θ hJq.1 hJcov
  have hrw : Rank3Witness ↥J₁ r := (hlay.trans hcc.1.symm).symm ▸ hcov
  exact ⟨planeF z u hadd hu1, J₁, hstd, hcent, hBF, hlay, hmark, hrw, hDB'⟩

private theorem p5Out_finish {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x z : G}
    {L J₁ F : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hDB' : Subgroup.closure {x, z} ≠ B)
    (hstd : LargeEvenStdSub 3 B x L (Subgroup.closure {x, z}) J₁)
    (hcent : Bs ⊓ Subgroup.centralizer (J₁ : Set G) = F)
    (hBF : B ⊓ F = Subgroup.closure {x, z}) {lab₀ : LargeEvenLabel} {r : ℕ}
    (hr1 : 1 ≤ r) (hm : LargeEvenTwoLocalRank 3 G < 2 * r + 1) (hrw : Rank3Witness ↥J₁ r)
    (hlay : J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)))
    (hmark : LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = lab₀)) :
    ∃ J₁ : Subgroup G, P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = lab₀) := by
  have hA1 := not_le_centralizer_of_inf_eq hBs.1 hcent hBF hDB'
  have h3 : 3 ∣ Nat.card J₁ := by
    obtain ⟨E, -, -, hEcard, -, -, -, -⟩ := hrw
    have hdvd : Nat.card E ∣ Nat.card J₁ := Subgroup.card_subgroup_dvd_card E
    exact (dvd_pow_self 3 (by omega) : 3 ∣ 3 ^ r).trans (hEcard ▸ hdvd)
  exact ⟨J₁, ⟨⟨hThm, hBs, hstd⟩, rfl, hN, h3, hA1, ⟨r, hm, hrw⟩⟩, hlay, hmark⟩

theorem p5Out_of_twE6Component {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x z : G} {L : Subgroup G} {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {u : G → NTPlane.X3} {φ : NTPlane.X3 → MulAut R}
    {J : Subgroup R} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x)
    (hzB : z ∈ B) (hznot : z ∉ Subgroup.zpowers x) (hB9 : 9 < Nat.card B)
    {lab₀ : LargeEvenLabel} {r : ℕ} (hr1 : 1 ≤ r)
    (hJq : CFSG.IsQuasisimple ↥J)
    (hJfix : J ≤ TauCeti.fixedSubgroup (φ (u z)).toMonoidHom)
    (hJnorm : (J.subgroupOf (TauCeti.fixedSubgroup (φ (u z)).toMonoidHom)).Normal)
    (hJsolv : IsSolvable (↥(TauCeti.fixedSubgroup (φ (u z)).toMonoidHom) ⧸
      J.subgroupOf (TauCeti.fixedSubgroup (φ (u z)).toMonoidHom)))
    (hJbig : 25920 < Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hJmark : LargeEvenMarking ↥J (fun lab _ _ _ _ _ => lab = lab₀))
    (hJdet : ∀ w : NTPlane.X3, (∀ j ∈ J, φ w j = j) ↔ ∃ c : ZMod 3, w = c • u z)
    (hJcov : ∀ (J₁ : Type) [Group J₁] [Finite J₁] (π : J₁ →* ↥J), Function.Surjective π →
      π.ker ≤ Subgroup.center J₁ → Rank3Witness J₁ r)
    (hm : LargeEvenTwoLocalRank 3 G < 2 * r + 1)
    (hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) (φ (u z)))
    (hψ : ∀ b ∈ Bs, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (φ (u b))) :
    ∃ J₁ : Subgroup G, P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = lab₀) := by
  obtain ⟨F, J₁, hstd, hcent, hBF, hlay, hmark, hrw, hDB'⟩ :=
    twE6_goodPlane_component hThm hBs hN hker hadd hu0 hzB hznot hB9 hJq hJfix hJnorm
      hJsolv hJbig hJmark hJdet hJcov hφ hψ
  exact p5Out_finish hThm hBs hN hDB' hstd hcent hBF hr1 hm hrw hlay hmark

end CFSG.StandardType.FrameRoute.TwE6Model

end
