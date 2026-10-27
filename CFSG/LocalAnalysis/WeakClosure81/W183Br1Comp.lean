module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs5
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCtx

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem br1_ker_rho_iff (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) (h : ↥H) :
    M.ρ h = 1 ↔ (h : G) ∈ kerMV V H := by
  rw [M.ρ_eq_one_iff h]
  exact ⟨fun hc => x.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨h.2, hc⟩, fun hk => hK hk⟩

theorem br1_shape_transport (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hLH : L ≤ H) {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y)
    (hQ : HasQuotShape L (kerMV V H : Set G) P) : P ↥(M.img L) := by
  obtain ⟨X, hX, φ, hφs, hφk, hPX⟩ := hQ
  letI : Group X := hX
  let ψ : ↥L →* LGL 2 M.W := M.ρ.comp (Subgroup.inclusion hLH)
  have hψ : ∀ k : ↥L, ψ k = M.ρ (Subgroup.inclusion hLH k) := fun _ => rfl
  let ψ' : ↥L →* ↥(M.img L) := ψ.codRestrict (M.img L) fun k => by
    rw [hψ k]
    exact M.mem_img.2 ⟨Subgroup.inclusion hLH k, k.2, rfl⟩
  have hψ'coe : ∀ k : ↥L, (ψ' k : LGL 2 M.W) = ψ k := fun _ => rfl
  have hψ's : Function.Surjective ψ' := by
    intro y
    obtain ⟨j, hj, hjρ⟩ := M.mem_img.1 y.2
    refine ⟨⟨(j : G), hj⟩, Subtype.ext ?_⟩
    show (ψ' ⟨(j : G), hj⟩ : LGL 2 M.W) = (y : LGL 2 M.W)
    rw [hψ'coe, hψ]
    have hinc : Subgroup.inclusion hLH ⟨(j : G), hj⟩ = j := Subtype.ext rfl
    rw [hinc, hjρ]
  have hψ'ker : ∀ k : ↥L, ψ' k = 1 ↔ (k : G) ∈ kerMV V H := by
    intro k
    have h1 : ψ' k = 1 ↔ ψ k = 1 := by
      rw [← Subtype.coe_inj, hψ'coe k]
      rfl
    rw [h1, hψ k]
    exact br1_ker_rho_iff x M hK _
  have hker : φ.ker = ψ'.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφk k, hψ'ker k]
    simp
  let e : X ≃* ↥(M.img L) :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ's))
  exact hP X ↥(M.img L) e hPX

theorem br1_comp_base (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G)) (hLT : L ⊔ D.T = H)
    (hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a)) :
    M.img L ≤ M.img H ∧ (∀ y ∈ M.img H, ∀ l ∈ M.img L, y * l * y⁻¹ ∈ M.img L) ∧
      IsSimpleGroup ↥(M.img L) ∧ (∃ a ∈ M.img L, ∃ b ∈ M.img L, a * b ≠ b * a) ∧
      (∀ y ∈ M.img H, (∀ l ∈ M.img L, y * l = l * y) → y = 1) := by
  have hDT : D.T ≤ H := x.hyp.hyp171.2.1
  have hnormLe : M.img H ≤ Subgroup.normalizer ((M.img L : Subgroup (LGL 2 M.W)) : Set _) :=
    M.img_le_normalizer (A := H) (S := L) le_rfl hLH hLn
  have hnorm : ∀ y ∈ M.img H, ∀ l ∈ M.img L, y * l * y⁻¹ ∈ M.img L := by
    intro y hy l hl
    exact (Subgroup.mem_normalizer_iff.mp (hnormLe hy) l).1 hl
  have hPinv : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y →
      (IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) →
      (IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a) := by
    intro X Y _ _ e h
    refine ⟨(MulEquiv.isSimpleGroup_congr e).mp h.1, ?_⟩
    obtain ⟨a, b, hab⟩ := h.2
    exact ⟨e a, e b, fun hh => hab (e.injective (by simpa using hh))⟩
  have hbase := br1_shape_transport x M hK hLH hPinv hQ
  have hsimple : IsSimpleGroup ↥(M.img L) := hbase.1
  have hnonab : ∃ a ∈ M.img L, ∃ b ∈ M.img L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hbase.2
    exact ⟨(a : LGL 2 M.W), a.2, (b : LGL 2 M.W), b.2, fun h => hab (Subtype.ext h)⟩
  haveI hXn : ((M.img L).subgroupOf (M.img H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (M.img_mono hLH)).mpr hnormLe
  have hsup : (M.img L).subgroupOf (M.img H) ⊔ (M.img D.T).subgroupOf (M.img H) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (M.img_mono hLH) (M.img_mono hDT),
      ← M.img_sup hLH hDT, hLT, Subgroup.subgroupOf_self]
  have hT2 : IsPGroup 2 ↥((M.img D.T).subgroupOf (M.img H)) :=
    (M.isPGroup_img x.hyp.isSylowIn_T.isPGroup).of_equiv
      (Subgroup.subgroupOfEquivOfLe (M.img_mono hDT)).symm
  have hcore : CFSG.pCore 2 ↥(M.img H) = ⊥ := by
    have h := pCoreOf_img_eq_bot x M
    rw [CFSG.Open.pCoreOf] at h
    exact Subgroup.map_injective (M.img H).subtype_injective (by rw [h, Subgroup.map_bot])
  have hO2 : ∀ N : Subgroup ↥(M.img H), N.Normal → IsPGroup 2 ↥N → N = ⊥ := by
    intro N hNn hNp
    have hle : N ≤ CFSG.pCore 2 ↥(M.img H) := by
      rw [CFSG.pCore_eq_iSup]
      exact le_iSup_of_le N (le_iSup_of_le hNn (le_iSup_of_le hNp le_rfl))
    rw [hcore] at hle
    exact le_bot_iff.mp hle
  have hZ : Subgroup.center ↥((M.img L).subgroupOf (M.img H)) = ⊥ := by
    let eL := Subgroup.subgroupOfEquivOfLe (M.img_mono hLH)
    haveI : IsSimpleGroup ↥((M.img L).subgroupOf (M.img H)) :=
      (MulEquiv.isSimpleGroup_congr eL).mpr hsimple
    refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative ?_
    intro hc
    obtain ⟨a, b, hab⟩ := hbase.2
    have h1 := hc.is_comm.comm (eL.symm a) (eL.symm b)
    exact hab (by simpa using congrArg eL h1)
  have hcentbot := w183_centralizer_eq_bot hZ hsup hT2 hO2
  refine ⟨M.img_mono hLH, hnorm, hsimple, hnonab, ?_⟩
  intro y hy hcomm
  have hyc : (⟨y, hy⟩ : ↥(M.img H)) ∈ Subgroup.centralizer
      (((M.img L).subgroupOf (M.img H) : Subgroup ↥(M.img H)) : Set ↥(M.img H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subtype.ext ((hcomm (l : LGL 2 M.W) hl).symm)
  have h1 : (⟨y, hy⟩ : ↥(M.img H)) = 1 := by
    rw [← Subgroup.mem_bot, ← hcentbot]
    exact hyc
  exact congrArg Subtype.val h1

private theorem w183_conjSubgroup_img {J E : Subgroup G} (M : ModDataE J E) {P : Subgroup G}
    (hP : P ≤ J) (j : ↥J) :
    conjSubgroup (M.img P) (M.ρ j) = M.img (conjSubgroup P (j : G)) := by
  have h := M.img_conj (A := P) hP j⁻¹
  rw [map_inv] at h
  have hcoe : (((j⁻¹ : ↥J) : G)) = (j : G)⁻¹ := rfl
  rw [hcoe, inv_inv] at h
  rw [← h]
  rfl

theorem br1_dynkin_of_H (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hLH : L ≤ H) {t : G} (htH : t ∈ H) (hD : ActsOnDynkinMod (kerMV V H) L t) :
    ActsOnDynkinMod ⊥ (M.img L) (M.ρ ⟨t, htH⟩) := by
  obtain ⟨htN, P, hP, hconj⟩ := hD
  obtain ⟨hKP, hPLt, hmax, S, hKS, hSL, hS2, hSodd, hnormSP⟩ := hP
  have hPLle : P ≤ L := hPLt.le
  have hKL : kerMV V H ≤ L := hKP.trans hPLle
  have hPH : P ≤ H := hPLle.trans hLH
  have hSH : S ≤ H := hSL.trans hLH
  have hρtN : M.ρ ⟨t, htH⟩ ∈ Subgroup.normalizer ((M.img L : Subgroup (LGL 2 M.W)) : Set _) :=
    M.img_le_normalizer (A := Subgroup.zpowers t) (S := L)
      (Subgroup.zpowers_le.mpr htH) hLH (Subgroup.zpowers_le.mpr htN)
      (M.mem_img.2 ⟨⟨t, htH⟩, Subgroup.mem_zpowers t, rfl⟩)
  refine ⟨hρtN, M.img P, ⟨bot_le, ?_, ?_, M.img S, bot_le, M.img_mono hSL, ?_, ?_, ?_⟩, ?_⟩
  ·
    have hnot : ¬ L ≤ P := fun h => hPLt.ne (le_antisymm hPLle h)
    obtain ⟨l, hlL, hlP⟩ := Set.not_subset.mp hnot
    have hmemL : M.ρ ⟨l, hLH hlL⟩ ∈ M.img L := M.mem_img.2 ⟨⟨l, hLH hlL⟩, hlL, rfl⟩
    have hmemP : M.ρ ⟨l, hLH hlL⟩ ∉ M.img P := by
      intro hmem
      obtain ⟨j, hjP, hjρ⟩ := M.mem_img.1 hmem
      have h1 : M.ρ (j⁻¹ * ⟨l, hLH hlL⟩) = 1 := by
        rw [map_mul, map_inv, hjρ]
        group
      have hKmem : ((j⁻¹ * ⟨l, hLH hlL⟩ : ↥H) : G) ∈ kerMV V H :=
        (br1_ker_rho_iff x M hK _).1 h1
      have hcoe : ((j⁻¹ * ⟨l, hLH hlL⟩ : ↥H) : G) = (j : G)⁻¹ * l := by
        simp
      rw [hcoe] at hKmem
      have hlP' : l ∈ P := by
        have hmem' := P.mul_mem (hjP : (j : G) ∈ P) (hKP hKmem)
        simpa using hmem'
      exact hlP hlP'
    exact lt_of_le_of_ne (M.img_mono hPLle) fun heq => hmemP (heq ▸ hmemL)
  ·
    intro Y hPY hYL
    have hHrange : M.img H = M.ρ.range := by
      unfold ModDataE.img
      rw [Subgroup.subgroupOf_self, Subgroup.map_top]
    have hYrange : Y ≤ M.ρ.range := by
      rw [← hHrange]
      exact hYL.trans (M.img_mono hLH)
    set Z : Subgroup G := (Y.comap M.ρ).map H.subtype with hZdef
    have hZsub : Z.subgroupOf H = Y.comap M.ρ := by
      rw [hZdef]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H) (Y.comap M.ρ)
    have hZimg : M.img Z = Y := by
      unfold ModDataE.img
      rw [hZsub]
      exact Subgroup.map_comap_eq_self hYrange
    have hPZ : P ≤ Z := by
      intro p hp
      rw [hZdef]
      exact Subgroup.mem_map.mpr ⟨⟨p, hLH (hPLle hp)⟩,
        Subgroup.mem_comap.mpr (hPY.le (M.mem_img.2 ⟨⟨p, hLH (hPLle hp)⟩, hp, rfl⟩)), rfl⟩
    have hPZlt : P < Z := lt_of_le_of_ne hPZ fun heq => (ne_of_lt hPY) (by rw [← hZimg, heq])
    have hZL : Z ≤ L := by
      intro z hz
      rw [hZdef] at hz
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hz
      rw [Subgroup.mem_comap] at hh
      obtain ⟨l, hlL, hlρ⟩ := M.mem_img.1 (hYL hh)
      have h1 : M.ρ (h * ⟨l, hLH hlL⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, hlρ]
        group
      have hKmem : ((h * ⟨l, hLH hlL⟩⁻¹ : ↥H) : G) ∈ kerMV V H :=
        (br1_ker_rho_iff x M hK _).1 h1
      have hcoe : ((h * ⟨l, hLH hlL⟩⁻¹ : ↥H) : G) = (h : G) * l⁻¹ := by
        simp
      rw [hcoe] at hKmem
      have hmem : (h : G) = ((h : G) * (l : G)⁻¹) * (l : G) := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      change (h : G) ∈ L
      rw [hmem]
      exact L.mul_mem (hKL hKmem) hlL
    rw [← hZimg, hmax Z hPZlt hZL]
  ·
    intro s hs
    obtain ⟨j, hjS, rfl⟩ := M.mem_img.1 hs
    obtain ⟨k, hk⟩ := hS2 (j : G) hjS
    refine ⟨k, Subgroup.mem_bot.mpr ?_⟩
    rw [← map_pow]
    exact (br1_ker_rho_iff x M hK (j ^ (2 ^ k))).2 (by simpa using hk)
  ·
    have hkerρ : M.ρ.ker = (kerMV V H).subgroupOf H := by
      ext h
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact br1_ker_rho_iff x M hK h
    have hrel : (M.img S).relIndex (M.img L) = S.relIndex L := by
      show ((S.subgroupOf H).map M.ρ).relIndex ((L.subgroupOf H).map M.ρ) = S.relIndex L
      rw [Subgroup.relIndex_map_map, hkerρ,
        sup_eq_left.mpr (Subgroup.subgroupOf_mono H hKS),
        sup_eq_left.mpr (Subgroup.subgroupOf_mono H hKL)]
      exact Subgroup.relIndex_subgroupOf hLH
    rw [hrel]
    exact hSodd
  ·
    have hnorm_le : M.img L ⊓
        Subgroup.normalizer ((M.img S : Subgroup (LGL 2 M.W)) : Set _) ≤ M.img P := by
      rintro r ⟨hrL, hrN⟩
      obtain ⟨j, hjL, rfl⟩ := M.mem_img.1 hrL
      have hjN : (j : G) ∈ Subgroup.normalizer (S : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · rintro x hx
          obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.1 hx
          have hsH : s ∈ H := hSH hsS
          have hmem : M.ρ j * M.ρ ⟨s, hsH⟩ * (M.ρ j)⁻¹ ∈ M.img S :=
            (Subgroup.mem_normalizer_iff.mp hrN (M.ρ ⟨s, hsH⟩)).1
              (M.mem_img.2 ⟨⟨s, hsH⟩, hsS, rfl⟩)
          obtain ⟨u, huS, hu⟩ := M.mem_img.1 hmem
          have h1 : M.ρ (j * ⟨s, hsH⟩ * j⁻¹ * u⁻¹) = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu]
            group
          have hKmem : ((j * ⟨s, hsH⟩ * j⁻¹ * u⁻¹ : ↥H) : G) ∈ kerMV V H :=
            (br1_ker_rho_iff x M hK _).1 h1
          have hcoe : ((j * ⟨s, hsH⟩ * j⁻¹ * u⁻¹ : ↥H) : G) =
              (j : G) * s * (j : G)⁻¹ * (u : G)⁻¹ := by
            simp
          rw [hcoe] at hKmem
          have hmem' : (j : G) * s * (j : G)⁻¹ ∈ S := by
            have := S.mul_mem (hKS hKmem) huS
            simpa [mul_assoc] using this
          simpa [MulAut.conj_apply] using hmem'
        · rw [Subgroup.card_map_of_injective (MulAut.conj (j : G)).injective]
      have hjP : (j : G) ∈ P := hnormSP ⟨hjL, hjN⟩
      exact M.mem_img.2 ⟨j, hjP, rfl⟩
    exact hnorm_le
  ·
    rintro lstar ⟨l, hlL, rfl⟩ hconjeq
    set g : ↥H := ⟨t, htH⟩⁻¹ * l with hgdef
    have hgcoe : (g : G) = t⁻¹ * (l : G) := by
      rw [hgdef]
      simp
    have h1 : M.img (conjSubgroup P (g : G)) = M.img P := by
      have h2 : conjSubgroup (M.img P) (M.ρ g) = M.img P := by
        rw [hgdef, map_mul, map_inv]
        exact hconjeq
      rwa [w183_conjSubgroup_img M hPH g] at h2
    have hQH : conjSubgroup P (g : G) ≤ H := by
      intro q hq
      rw [mem_conjSubgroup_iff] at hq
      have hq' : q = (g : G)⁻¹ * ((g : G) * q * (g : G)⁻¹) * (g : G) := by group
      rw [hq']
      exact H.mul_mem (H.mul_mem (H.inv_mem g.2) (hLH (hPLle hq))) g.2
    have hQK : kerMV V H ≤ conjSubgroup P (g : G) := by
      intro k hk
      rw [mem_conjSubgroup_iff]
      exact hKP (conj_mem_kerMV g.2 hk)
    have hQleP : conjSubgroup P (g : G) ≤ P := by
      intro q hq
      have hqH : q ∈ H := hQH hq
      have hmem : M.ρ ⟨q, hqH⟩ ∈ M.img (conjSubgroup P (g : G)) :=
        M.mem_img.2 ⟨⟨q, hqH⟩, hq, rfl⟩
      rw [h1] at hmem
      obtain ⟨p, hpP, hpρ⟩ := M.mem_img.1 hmem
      have h1' : M.ρ (⟨q, hqH⟩ * p⁻¹) = 1 := by
        rw [map_mul, map_inv, hpρ]
        group
      have hKmem : ((⟨q, hqH⟩ * p⁻¹ : ↥H) : G) ∈ kerMV V H :=
        (br1_ker_rho_iff x M hK _).1 h1'
      have hcoe : ((⟨q, hqH⟩ * p⁻¹ : ↥H) : G) = q * (p : G)⁻¹ := by
        simp
      rw [hcoe] at hKmem
      have hmem' : q = (q * (p : G)⁻¹) * p := by group
      rw [hmem']
      exact P.mul_mem (hKP hKmem) hpP
    have hPleQ : P ≤ conjSubgroup P (g : G) := by
      intro p hpP
      have hpL : (p : G) ∈ L := hPLle hpP
      have hpimg : M.ρ ⟨p, hLH hpL⟩ ∈ M.img P :=
        M.mem_img.2 ⟨⟨p, hLH hpL⟩, hpP, rfl⟩
      rw [← h1] at hpimg
      obtain ⟨q, hqQ, hqρ⟩ := M.mem_img.1 hpimg
      have h1' : M.ρ (⟨p, hLH hpL⟩ * q⁻¹) = 1 := by
        rw [map_mul, map_inv, hqρ]
        group
      have hKmem : ((⟨p, hLH hpL⟩ * q⁻¹ : ↥H) : G) ∈ kerMV V H :=
        (br1_ker_rho_iff x M hK _).1 h1'
      have hcoe : ((⟨p, hLH hpL⟩ * q⁻¹ : ↥H) : G) = p * (q : G)⁻¹ := by
        simp
      rw [hcoe] at hKmem
      have hmem' : p = (p * (q : G)⁻¹) * q := by group
      rw [hmem']
      exact (conjSubgroup P (g : G)).mul_mem (hQK hKmem) hqQ
    have hQeq : conjSubgroup P (g : G) = P := le_antisymm hQleP hPleQ
    rw [hgcoe] at hQeq
    exact hconj (l : G) hlL hQeq

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
