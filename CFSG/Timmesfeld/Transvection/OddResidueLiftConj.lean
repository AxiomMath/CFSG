module

public import CFSG.Timmesfeld.Transvection.OddResidueLift
import CFSG.GroupTheory.OddCentralQuotient
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3
public import CFSG.Timmesfeld.Transvection.OddResidueTrans

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.CurtisTits CFSG.LieType.BorelTits
open scoped commutatorElement CharTwo

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

section Certificates


private theorem exists_sylow_image_heisenberg
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {α : SU (unitaryInvolution F 2 n) 3 →* ↥(residueGroup Δ P Q k)}
    (hαsurj : Function.Surjective α) :
    ∃ S : Sylow 2 (residueQuotient Δ P Q k),
      (S : Subgroup (residueQuotient Δ P Q k)) =
        (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map
          ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α) := by
  have h4 : 4 ≤ 2 ^ n := by
    rw [← hcard (P k) (hF.toIsFrame.memP k)]
    exact hq (P k) (hF.toIsFrame.memP k)
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0] at h4
      norm_num at h4
    · exact hnpos
  let X : Subgroup (SU (unitaryInvolution F 2 n) 3) :=
    UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)
  let ρ : SU (unitaryInvolution F 2 n) 3 →* residueQuotient Δ P Q k :=
    (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α
  have hXp : IsPGroup 2 X := UC22.uc22pwsu3X_isPGroup hFn
  have hXsurj : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective (Subgroup.center
      ↥(residueGroup Δ P Q k))).comp hαsurj
  have hXidx : ¬ 2 ∣ (X.map ρ).index := by
    intro hdvd2
    have hoddX : Odd X.index := by
      have hnot : ¬ 2 ∣ X.index := UC22.uc22pwsu3X_index hn1 hFn
      exact Nat.not_even_iff_odd.1 (by rwa [even_iff_two_dvd])
    exact hoddX.not_two_dvd_nat (hdvd2.trans (Subgroup.index_map_dvd X hXsurj))
  have hXmapP : IsPGroup 2 (X.map ρ) := hXp.map ρ
  refine ⟨hXmapP.toSylow hXidx, ?_⟩
  exact IsPGroup.toSylow_coe hXmapP hXidx

private theorem exists_conjSub_map_eq_sylow_image
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q k)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {α : SU (unitaryInvolution F 2 n) 3 →* ↥(residueGroup Δ P Q k)}
    (hαsurj : Function.Surjective α) :
    ∃ (g : SU (unitaryInvolution F 2 n) 3)
      (TP : Sylow 2 (residueQuotient Δ P Q k)),
      (TP : Subgroup (residueQuotient Δ P Q k)) =
          (conjSub (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)) g).map
            ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α) ∧
        ((P k).subgroupOf (residueGroup Δ P Q k)).map
            (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) =
          (Subgroup.center (TP : Subgroup (residueQuotient Δ P Q k))).map
            (TP : Subgroup (residueQuotient Δ P Q k)).subtype := by
  classical
  haveI : Finite H := h.finite
  let L : Subgroup H := residueGroup Δ P Q k
  let π : ↥L →* residueQuotient Δ P Q k := QuotientGroup.mk' (Subgroup.center ↥L)
  let ρ : SU (unitaryInvolution F 2 n) 3 →* residueQuotient Δ P Q k := π.comp α
  let X : Subgroup (SU (unitaryInvolution F 2 n) 3) :=
    UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)
  obtain ⟨S, hSP⟩ := exists_sylow_image_heisenberg hq hF hFn hcard hαsurj
  change (S : Subgroup (residueQuotient Δ P Q k)) = X.map ρ at hSP
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  obtain ⟨TP, hTP⟩ := IsMaxFrame.map_mem_frameResidue_eq_center
    (Δ := Δ) (P := P) (Q := Q) (k := k) h hML hq hF hns hP
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq (residueQuotient Δ P Q k) S TP
  obtain ⟨g', hg'⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) l
  obtain ⟨g, hg⟩ := hαsurj g'
  have hπg : π (α g) = l := by rw [hg, hg']
  have hρg : ρ g = l := hπg
  have hconj : ∀ x : SU (unitaryInvolution F 2 n) 3,
      ρ (MulAut.conj g x) = MulAut.conj l (ρ x) := by
    intro x
    simp only [MulAut.conj_apply, map_mul, map_inv, hρg]
  have hcompeq : (MulAut.conj l).toMonoidHom.comp ρ =
      ρ.comp (MulAut.conj g).toMonoidHom :=
    MonoidHom.ext fun x => (hconj x).symm
  have hTPX : (TP : Subgroup (residueQuotient Δ P Q k)) = (conjSub X g).map ρ := by
    have hcoe : (TP : Subgroup (residueQuotient Δ P Q k)) =
        (S : Subgroup (residueQuotient Δ P Q k)).map
          (MulAut.conj l).toMonoidHom := by
      rw [← hl, Sylow.coe_subgroup_smul]
      rfl
    rw [hcoe, hSP, Subgroup.map_map, hcompeq, ← Subgroup.map_map]
  exact ⟨g, TP, hTPX, hTP⟩

private theorem map_conjSub_su3Top_le_center
    (hFn : Nat.card F = (2 ^ n) ^ 2)
    {α : SU (unitaryInvolution F 2 n) 3 →* ↥(residueGroup Δ P Q k)}
    {g : SU (unitaryInvolution F 2 n) 3} {TP : Sylow 2 (residueQuotient Δ P Q k)}
    (hTPX : (TP : Subgroup (residueQuotient Δ P Q k)) =
      (conjSub (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)) g).map
        ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α)) :
    (conjSub (su3Top (unitaryInvolution F 2 n)) g).map
        ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α) ≤
      (Subgroup.center (TP : Subgroup (residueQuotient Δ P Q k))).map
        (TP : Subgroup (residueQuotient Δ P Q k)).subtype := by
  let ρ : SU (unitaryInvolution F 2 n) 3 →* residueQuotient Δ P Q k :=
    (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α
  let X : Subgroup (SU (unitaryInvolution F 2 n) 3) :=
    UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)
  change (TP : Subgroup (residueQuotient Δ P Q k)) = (conjSub X g).map ρ at hTPX
  have hcommTop : Commuting (su3Top (unitaryInvolution F 2 n)) X := by
    intro y hy x hx
    obtain ⟨β, hβ, rfl⟩ := (mem_su3Top_iff_Y (σ := unitaryInvolution F 2 n)).1 hy
    exact (UC22.uc22pwsu3Y_comm (unitaryInvolution_involutive hFn) hx β hβ).symm
  have hcommMap : Commuting ((conjSub (su3Top (unitaryInvolution F 2 n)) g).map ρ)
      ((conjSub X g).map ρ) := ModelRank.commuting_map ρ (hcommTop.conjSub g)
  intro a ha
  have haTP : a ∈ (TP : Subgroup (residueQuotient Δ P Q k)) := by
    rw [hTPX]
    exact Subgroup.map_mono (Subgroup.map_mono (su3Top_le_X
      (unitaryInvolution_involutive hFn))) ha
  refine Subgroup.mem_map.2 ⟨⟨a, haTP⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro t
  apply Subtype.ext
  change (t : residueQuotient Δ P Q k) * a = a * (t : residueQuotient Δ P Q k)
  have htX : (t : residueQuotient Δ P Q k) ∈ (conjSub X g).map ρ := by
    rw [← hTPX]
    exact t.2
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.1 htX
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 ha
  have hx' : ρ x ∈ (conjSub X g).map ρ := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hy' : ρ y ∈ (conjSub (su3Top (unitaryInvolution F 2 n)) g).map ρ :=
    Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  rw [← hxeq, ← hyeq]
  exact (hcommMap (ρ y) hy' (ρ x) hx').symm

private theorem sq_eq_one_of_mem_conjSub_of_mem_ker
    (hFn : Nat.card F = (2 ^ n) ^ 2)
    {α : SU (unitaryInvolution F 2 n) 3 →* ↥(residueGroup Δ P Q k)}
    (hαπodd : Odd (Nat.card
      ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α).ker))
    {g : SU (unitaryInvolution F 2 n) 3} {x : SU (unitaryInvolution F 2 n) 3}
    (hxXg : x ∈ conjSub (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)) g)
    (hx2ker : x * x ∈
      ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α).ker) :
    x * x = 1 := by
  let X : Subgroup (SU (unitaryInvolution F 2 n) 3) :=
    UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)
  let ρ : SU (unitaryInvolution F 2 n) 3 →* residueQuotient Δ P Q k :=
    (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α
  change x ∈ conjSub X g at hxXg
  change x * x ∈ ρ.ker at hx2ker
  have hK : IsPGroup 2 (conjSub X g) :=
    (UC22.uc22pwsu3X_isPGroup hFn).map (MulAut.conj g).toMonoidHom
  obtain ⟨m, hm⟩ := hK.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (conjSub X g)) (Nat.card ρ.ker) := by
    rw [hm]
    exact Nat.Coprime.pow_left m hαπodd.coprime_two_right.symm
  have hinf : conjSub X g ⊓ ρ.ker = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hmem : x * x ∈ conjSub X g ⊓ ρ.ker :=
    ⟨Subgroup.mul_mem _ hxXg hxXg, hx2ker⟩
  rwa [hinf] at hmem

private theorem center_le_map_conjSub_su3Top
    (h : TransvectionHyp H Δ) (hF : IsMaxFrame Δ P Q)
    (hFn : Nat.card F = (2 ^ n) ^ 2)
    {α : SU (unitaryInvolution F 2 n) 3 →* ↥(residueGroup Δ P Q k)}
    (hαπodd : Odd (Nat.card
      ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α).ker))
    {g : SU (unitaryInvolution F 2 n) 3} {TP : Sylow 2 (residueQuotient Δ P Q k)}
    (hTP : ((P k).subgroupOf (residueGroup Δ P Q k)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) =
      (Subgroup.center (TP : Subgroup (residueQuotient Δ P Q k))).map
        (TP : Subgroup (residueQuotient Δ P Q k)).subtype)
    (hTPX : (TP : Subgroup (residueQuotient Δ P Q k)) =
      (conjSub (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)) g).map
        ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α)) :
    ((P k).subgroupOf (residueGroup Δ P Q k)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) ≤
      (conjSub (su3Top (unitaryInvolution F 2 n)) g).map
        ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α) := by
  haveI : Finite H := h.finite
  let X : Subgroup (SU (unitaryInvolution F 2 n) 3) :=
    UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)
  let ρ : SU (unitaryInvolution F 2 n) 3 →* residueQuotient Δ P Q k :=
    (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α
  change (TP : Subgroup (residueQuotient Δ P Q k)) = (conjSub X g).map ρ at hTPX
  intro y hy
  have hyZ : y ∈ (Subgroup.center (TP : Subgroup (residueQuotient Δ P Q k))).map
      (TP : Subgroup (residueQuotient Δ P Q k)).subtype := by
    rw [← hTP]
    exact hy
  have hyT : y ∈ (TP : Subgroup (residueQuotient Δ P Q k)) :=
    Subgroup.map_subtype_le _ hyZ
  have hyT' : y ∈ (conjSub X g).map ρ := by
    rw [← hTPX]
    exact hyT
  have hy2 : y * y = 1 := by
    obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.1 hy
    have hp2 : p * p = 1 := by
      apply Subtype.ext
      exact h.cls.root.mul_self (P k) (hF.toIsFrame.memP k) (p : H) hp
    rw [← hpy]
    simpa using congrArg (QuotientGroup.mk'
      (Subgroup.center ↥(residueGroup Δ P Q k))) hp2
  obtain ⟨x, hxXg, hxy⟩ := Subgroup.mem_map.1 hyT'
  have hx2ker : x * x ∈ ρ.ker := by
    simpa [MonoidHom.mem_ker, map_mul, hxy, hy2]
  have hx2 : x * x = 1 :=
    sq_eq_one_of_mem_conjSub_of_mem_ker hFn hαπodd hxXg hx2ker
  obtain ⟨x', hx', hxeq⟩ := Subgroup.mem_map.1 hxXg
  have hxeq' : (MulAut.conj g) x' = x := hxeq
  have hx'2 : x' * x' = 1 := by
    apply (MulAut.conj g).injective
    simpa [hxeq', hx2] using map_mul (MulAut.conj g) x' x'
  obtain ⟨β, hβ, hx'Y⟩ := UC22.uc22pwsu3_exists_Y_of_sq
    (unitaryInvolution_involutive hFn) hx' hx'2
  have hmemTop : MulAut.conj g (UC22.uc22pwsu3Y β hβ) ∈
      conjSub (su3Top (unitaryInvolution F 2 n)) g := by
    refine Subgroup.mem_map.2 ⟨UC22.uc22pwsu3Y β hβ, ?_, rfl⟩
    exact (mem_su3Top_iff_Y (σ := unitaryInvolution F 2 n)).2 ⟨β, hβ, rfl⟩
  refine Subgroup.mem_map.2 ⟨MulAut.conj g (UC22.uc22pwsu3Y β hβ), hmemTop, ?_⟩
  rw [hx'Y] at hxeq
  have hxeq'' : (MulAut.conj g) (UC22.uc22pwsu3Y β hβ) = x := hxeq
  rw [hxeq'', hxy]

private theorem exists_conjSub_map_eq_residueQuotient
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q k)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {α : SU (unitaryInvolution F 2 n) 3 →* ↥(residueGroup Δ P Q k)}
    (hαsurj : Function.Surjective α)
    (hαπodd : Odd (Nat.card
      ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α).ker)) :
    ∃ g : SU (unitaryInvolution F 2 n) 3,
      (conjSub (su3Top (unitaryInvolution F 2 n)) g).map
          ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α) =
        ((P k).subgroupOf (residueGroup Δ P Q k)).map
          (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) := by
  obtain ⟨g, TP, hTPX, hTP⟩ :=
    exists_conjSub_map_eq_sylow_image h hML hq hF hns hFn hcard hαsurj
  refine ⟨g, le_antisymm ?_ ?_⟩
  · exact (map_conjSub_su3Top_le_center hFn hTPX).trans (le_of_eq hTP.symm)
  · exact center_le_map_conjSub_su3Top h hF hFn hαπodd hTP hTPX

private theorem map_eq_P_of_map_eq_residueQuotient
    (h : TransvectionHyp H Δ) (hF : IsMaxFrame Δ P Q)
    {α : SU (unitaryInvolution F 2 n) 3 →* ↥(residueGroup Δ P Q k)}
    (hαsurj : Function.Surjective α)
    (hαπodd : Odd (Nat.card
      ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α).ker))
    {g : SU (unitaryInvolution F 2 n) 3}
    (hZeq : (conjSub (su3Top (unitaryInvolution F 2 n)) g).map
        ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α) =
      ((P k).subgroupOf (residueGroup Δ P Q k)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)))) :
    (conjSub (su3Top (unitaryInvolution F 2 n)) g).map
        ((residueGroup Δ P Q k).subtype.comp α) = P k := by
  classical
  haveI : Finite H := h.finite
  let L : Subgroup H := residueGroup Δ P Q k
  let π : ↥L →* residueQuotient Δ P Q k := QuotientGroup.mk' (Subgroup.center ↥L)
  let A : Subgroup ↥L := (P k).subgroupOf L
  let B : Subgroup ↥L := (conjSub (su3Top (unitaryInvolution F 2 n)) g).map α
  have hZeq' : B.map π = A.map π := by
    rw [Subgroup.map_map]
    exact hZeq
  have hsup : A ⊔ Subgroup.center ↥L = B ⊔ Subgroup.center ↥L := by
    have h := (Subgroup.map_eq_map_iff (f := π)).mp hZeq'
    rw [QuotientGroup.ker_mk'] at h
    exact h.symm
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    have hZle : Subgroup.center ↥L ≤ (π.comp α).ker.map α := by
      intro z hz
      obtain ⟨s, rfl⟩ := hαsurj z
      refine Subgroup.mem_map.2 ⟨s, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center ↥L) (α s)).2 hz
    exact Odd.of_dvd_nat hαπodd
      ((Subgroup.card_dvd_of_le hZle).trans (Subgroup.card_map_dvd ((π.comp α).ker) α))
  have hAexp : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    apply Subtype.ext
    simpa using h.cls.root.mul_self (P k) (hF.toIsFrame.memP k) (a : H) ha
  have hBexp : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hb
    have hs2 : s * s = 1 := by
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hs
      rw [← hyeq, ← map_mul, su3Top_mul_self hy, map_one]
    rw [← map_mul, hs2, map_one]
  have h2 : ∀ C : Subgroup ↥L, (∀ c ∈ C, c * c = 1) → IsPGroup 2 C := fun C hC x =>
    ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (hC x x.2)⟩
  have heq : A = B :=
    CFSG.GroupTheory.eq_of_sup_eq_of_le_center le_rfl hZodd (h2 A hAexp) (h2 B hBexp) hsup
  have hAeq : A.map L.subtype = P k :=
    Subgroup.map_subgroupOf_eq_of_le
      (frameResidue_le_residueGroup (hF.toIsFrame.memP_frameResidue k))
  have hBeq : B.map L.subtype =
      (conjSub (su3Top (unitaryInvolution F 2 n)) g).map (L.subtype.comp α) := by
    rw [Subgroup.map_map]
  rw [← hBeq, ← hAeq, heq]

private theorem mem_frameResidue_iff_exists_conjSub_map
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k)
    {g₀ : SU (unitaryInvolution F 2 n) 3}
    (hg₀ : (conjSub (su3Top (unitaryInvolution F 2 n)) g₀).map θ = P k) :
    ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g : SU (unitaryInvolution F 2 n) 3,
        X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ := by
  intro X
  constructor
  · intro hX
    obtain ⟨l, hlL, hl⟩ :=
      IsMaxFrame.exists_conjSub_eq_of_mem_frameResidue h hML hq hF k hX
    have hlrange : l ∈ θ.range := by rw [hθr]; exact hlL
    obtain ⟨s, rfl⟩ := hlrange
    refine ⟨s * g₀, ?_⟩
    rw [← hl, ← hg₀, ModelRank.conjSub_map, ← conjSub_mul]
  · rintro ⟨g, rfl⟩
    have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
    have hform : (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ =
        conjSub (P k) (θ (g * g₀⁻¹)) := by
      rw [← hg₀, ModelRank.conjSub_map, ← conjSub_mul]
      congr 2
      group
    rw [hform]
    refine conjSub_mem_frameResidue h.cls hP ?_
    rw [← hθr]
    exact MonoidHom.mem_range.2 ⟨g * g₀⁻¹, rfl⟩

private theorem precomp_properties
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k)
    (hθk : θ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 n) 3))
    (hθodd : Odd (Nat.card θ.ker))
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g : SU (unitaryInvolution F 2 n) 3,
        X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {a : SU (unitaryInvolution F 2 n) 3}
    (ha : (conjSub (su3Top (unitaryInvolution F 2 n)) a).map θ = P k) :
    (θ.comp (MulAut.conj a).toMonoidHom).range = residueGroup Δ P Q k ∧
      (θ.comp (MulAut.conj a).toMonoidHom).ker ≤
        Subgroup.center (SU (unitaryInvolution F 2 n) 3) ∧
      Odd (Nat.card (θ.comp (MulAut.conj a).toMonoidHom).ker) ∧
      (su3Top (unitaryInvolution F 2 n)).map (θ.comp (MulAut.conj a).toMonoidHom) = P k ∧
      ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
        ∃ g : SU (unitaryInvolution F 2 n) 3,
          X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map
            (θ.comp (MulAut.conj a).toMonoidHom) := by
  have hform : ∀ e : SU (unitaryInvolution F 2 n) 3,
      (conjSub (su3Top (unitaryInvolution F 2 n)) e).map
          (θ.comp (MulAut.conj a).toMonoidHom) =
        (conjSub (su3Top (unitaryInvolution F 2 n)) (a * e)).map θ := by
    intro e
    rw [← Subgroup.map_map, conjSub_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj a).surjective,
      Subgroup.map_top, hθr]
  · have hker : (θ.comp (MulAut.conj a).toMonoidHom).ker =
        (θ.ker).map ((MulAut.conj a).symm : SU (unitaryInvolution F 2 n) 3 →*
          SU (unitaryInvolution F 2 n) 3) := by
      simpa using MonoidHom.ker_comp_mulEquiv θ (MulAut.conj a)
    rw [hker]
    calc (θ.ker).map ((MulAut.conj a).symm : SU (unitaryInvolution F 2 n) 3 →*
          SU (unitaryInvolution F 2 n) 3) ≤
        (Subgroup.center (SU (unitaryInvolution F 2 n) 3)).map
          ((MulAut.conj a).symm : SU (unitaryInvolution F 2 n) 3 →*
            SU (unitaryInvolution F 2 n) 3) := Subgroup.map_mono hθk
      _ = Subgroup.center (SU (unitaryInvolution F 2 n) 3) :=
        Subgroup.map_center_eq (MulAut.conj a).symm
  · have hker : (θ.comp (MulAut.conj a).toMonoidHom).ker =
        (θ.ker).map ((MulAut.conj a).symm : SU (unitaryInvolution F 2 n) 3 →*
          SU (unitaryInvolution F 2 n) 3) := by
      simpa using MonoidHom.ker_comp_mulEquiv θ (MulAut.conj a)
    rw [hker, Subgroup.card_map_of_injective (MulAut.conj a).symm.injective]
    exact hθodd
  · calc (su3Top (unitaryInvolution F 2 n)).map (θ.comp (MulAut.conj a).toMonoidHom)
        = (conjSub (su3Top (unitaryInvolution F 2 n)) (1 :
            SU (unitaryInvolution F 2 n) 3)).map (θ.comp (MulAut.conj a).toMonoidHom) := by
          simp
      _ = (conjSub (su3Top (unitaryInvolution F 2 n)) (a * 1)).map θ := hform 1
      _ = P k := by simpa using ha
  · intro X
    rw [hθmem X]
    constructor
    · rintro ⟨e, he⟩
      exact ⟨a⁻¹ * e, by rw [hform, mul_inv_cancel_left, he]⟩
    · rintro ⟨e, he⟩
      exact ⟨a * e, by rw [← hform, he]⟩

private theorem exists_su3_residue_normalize
    (h : TransvectionHyp H Δ) (hF : IsMaxFrame Δ P Q)
    (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k)
    (hθk : θ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 n) 3))
    (hθodd : Odd (Nat.card θ.ker))
    (hθtop : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g : SU (unitaryInvolution F 2 n) 3,
        X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ) :
    ∃ θ' : SU (unitaryInvolution F 2 n) 3 →* H,
      θ'.range = residueGroup Δ P Q k ∧
        θ'.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 n) 3) ∧
        Odd (Nat.card θ'.ker) ∧
        (su3Top (unitaryInvolution F 2 n)).map θ' = P k ∧
        (su3Bot (unitaryInvolution F 2 n)).map θ' = Q k ∧
        ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
          ∃ g : SU (unitaryInvolution F 2 n) 3,
            X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ' := by
  classical
  haveI : Finite H := h.finite
  have hσ := unitaryInvolution_involutive hFn
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hFn
  obtain ⟨g', hg'⟩ := (hθmem (Q k)).1 (hF.toIsFrame.memQ_frameResidue k)
  have hbruhat := UC22.uc22pwsu3_bruhat hσ (UC22.uc22pwsu3_hnorm hFn)
    (rankOne_three_eq_top hFn) hζ g'
  rcases hbruhat with ⟨hh, hhh, u, hu, rfl⟩ | ⟨u, hu, hh, hhh, v, hv, rfl⟩
  · have hconj : conjSub (su3Top (unitaryInvolution F 2 n)) (hh * u) =
        su3Top (unitaryInvolution F 2 n) := by
      rw [conjSub_mul, conjSub_su3Top_of_mem_X hσ hu, conjSub_su3Top_of_mem_H hσ hhh]
    have hQ : Q k = P k := by rw [hg', hconj, hθtop]
    exact absurd hQ.symm (hF.opposite k).1
  · have hconj : conjSub (su3Top (unitaryInvolution F 2 n))
        (u * UC22.uc22pwsu3W hσ ζ * hh * v) =
        conjSub (su3Bot (unitaryInvolution F 2 n)) u := by
      rw [conjSub_mul, conjSub_su3Top_of_mem_X hσ hv,
        conjSub_mul, conjSub_su3Top_of_mem_H hσ hhh,
        conjSub_mul, conjSub_su3Top_W hσ hζ]
    have hQ : (conjSub (su3Bot (unitaryInvolution F 2 n)) u).map θ = Q k := by
      rw [← hconj, ← hg']
    have htopu : (conjSub (su3Top (unitaryInvolution F 2 n)) u).map θ = P k := by
      rw [conjSub_su3Top_of_mem_X hσ hu, hθtop]
    obtain ⟨hr, hk, hodd, htop, hmem⟩ :=
      precomp_properties (Δ := Δ) (P := P) (Q := Q) (k := k) hθr hθk hθodd hθmem htopu
    refine ⟨θ.comp (MulAut.conj u).toMonoidHom, hr, hk, hodd, htop, ?_, hmem⟩
    change (su3Bot (unitaryInvolution F 2 n)).map
      (θ.comp (MulAut.conj u).toMonoidHom) = Q k
    rw [← Subgroup.map_map]
    exact hQ

end Certificates

theorem IsMaxFrame.exists_su3_residue [Finite H]
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q k)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) :
    ∃ θ : SU (unitaryInvolution F 2 n) 3 →* H,
      θ.range = residueGroup Δ P Q k ∧ θ.ker ≤ Subgroup.center _ ∧ Odd (Nat.card θ.ker) ∧
      (su3Top _).map θ = P k ∧ (su3Bot _).map θ = Q k ∧
      ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔ ∃ g, X = (conjSub (su3Top _) g).map θ := by
  classical
  obtain ⟨α, hαsurj, hαker, hαodd, hαπker, hαπodd⟩ :=
    IsMaxFrame.exists_su3_cover (Δ := Δ) (P := P) (Q := Q) (k := k)
      h hML hq hF hns hFn hcard
  let L : Subgroup H := residueGroup Δ P Q k
  let θ₀ : SU (unitaryInvolution F 2 n) 3 →* H := L.subtype.comp α
  have hθ₀r : θ₀.range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hαsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  have hθ₀k : θ₀.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 n) 3) := by
    rw [MonoidHom.ker_comp_of_injective α L.subtype L.subtype_injective]
    exact hαker
  have hθ₀odd : Odd (Nat.card θ₀.ker) := by
    rw [MonoidHom.ker_comp_of_injective α L.subtype L.subtype_injective]
    exact hαodd
  obtain ⟨g, hZeq⟩ :=
    exists_conjSub_map_eq_residueQuotient h hML hq hF hns hFn hcard hαsurj hαπodd
  have hg : (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ₀ = P k :=
    map_eq_P_of_map_eq_residueQuotient h hF hαsurj hαπodd hZeq
  have hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g' : SU (unitaryInvolution F 2 n) 3,
        X = (conjSub (su3Top (unitaryInvolution F 2 n)) g').map θ₀ :=
    mem_frameResidue_iff_exists_conjSub_map h hML hq hF hθ₀r hg
  obtain ⟨h₁r, h₁k, h₁odd, h₁top, h₁mem⟩ :=
    precomp_properties (Δ := Δ) (P := P) (Q := Q) (k := k) hθ₀r hθ₀k hθ₀odd hmem hg
  exact exists_su3_residue_normalize h hF hFn h₁r h₁k h₁odd h₁top h₁mem

end CFSG.Timmesfeld.Transvection
