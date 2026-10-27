module

public import CFSG.RankThree.GF2n.Parrott.Section3Lemma34OtherE16
public import CFSG.GH74.PartII.Lemma22E16Alt5
import CFSG.RankThree.GF2n.Parrott.Section3Lemma34Local
import CFSG.GroupTheory.CentralizerSylowFusion
import CFSG.RankThree.GF2n.Parrott.Section3Fusion
public import CFSG.Quasithin.Recognition.L34CIT.Config

public section

namespace CFSG.RankThree.GF2n.Parrott

open Subgroup CFSG.Open

variable {K : Type} [Group K] [Finite K] {B D : Subgroup K}

private theorem isTwoE16_swap {P : Type} [Group P] {A B : Subgroup P}
    (h : CFSG.OddStandard.ThmC.T.IsTwoE16 P A B) :
    CFSG.OddStandard.ThmC.T.IsTwoE16 P B A where
  normal_left := h.normal_right
  normal_right := h.normal_left
  inf_eq := by rw [inf_comm, h.inf_eq]
  sup_eq := by rw [sup_comm, h.sup_eq]
  ne := h.ne.symm
  card_center := h.card_center
  card_left := h.card_right
  card_right := h.card_left
  sq_left := h.sq_right
  sq_right := h.sq_left
  comm_left := h.comm_right
  comm_right := h.comm_left
  sq_iff := fun x => by rw [h.sq_iff x, or_comm]
  le_or := fun E hE => by
    rcases h.le_or E hE with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  card_le := h.card_le
  eq_or := fun E hE hc => by
    rcases h.eq_or E hE hc with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  centralizer_left := h.centralizer_right
  centralizer_right := h.centralizer_left
  swap := by
    obtain ⟨φ, hφ⟩ := h.swap
    refine ⟨φ.symm, ?_⟩
    have h := congrArg (Subgroup.comap φ.symm.toMonoidHom) hφ
    simpa [Subgroup.comap_comap] using h.symm

private theorem card_centralizer_eq_sixtyFour_of_mem
    (hDB : D ≤ B) (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥B →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → centralizer ({d} : Set K) ≤ B)
    {d : K} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Nat.card (centralizer ({d} : Set K)) = 64 := by
  obtain ⟨π, hπs, hπk⟩ := hπ
  have hk16 : Nat.card ↥π.ker = 16 := by
    rw [hπk]
    calc Nat.card ↥(D.subgroupOf B) = Nat.card ↥D :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
      _ = 16 := hD16
  have htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 →
      ∃ g : ↥B, g * a * g⁻¹ = b := by
    intro a ha b hb ha1 hb1
    rw [hπk] at ha hb
    obtain ⟨g, hg, hgab⟩ :=
      hTrans a ha b hb (fun h => ha1 (Subtype.ext h)) (fun h => hb1 (Subtype.ext h))
    exact ⟨⟨g, hg⟩, Subtype.ext hgab⟩
  have hdker : (⟨d, hDB hd⟩ : ↥B) ∈ π.ker := by rw [hπk]; exact hd
  have hd1' : (⟨d, hDB hd⟩ : ↥B) ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hB := CFSG.GH74.PartII.card_centralizer_eq_64_of_e16_alt5 hπs hk16 htr hdker hd1'
  have hsub : (Subgroup.centralizer ({d} : Set K)).subgroupOf B =
      Subgroup.centralizer ({(⟨d, hDB hd⟩ : ↥B)} : Set ↥B) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  calc Nat.card (Subgroup.centralizer ({d} : Set K))
      = Nat.card ↥((Subgroup.centralizer ({d} : Set K)).subgroupOf B) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hCent d hd hd1)).toEquiv).symm
    _ = Nat.card ↥(Subgroup.centralizer ({(⟨d, hDB hd⟩ : ↥B)} : Set ↥B)) := by rw [hsub]
    _ = 64 := hB

private theorem normalizer_eq_of_e16_alt5
    (hDB : D ≤ B) (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥B →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → centralizer ({d} : Set K) ≤ B) :
    normalizer (D : Set K) = B := by
  obtain ⟨d₀, hd₀D, hd₀1, -⟩ :=
    exists_mem_ne_one_ne_of_two_lt_card (D := D) (by rw [hD16]; norm_num) 1
  obtain ⟨π, -, hπk⟩ := hπ
  have hDnormB : ∀ g ∈ B, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    have hd' : (⟨d, hDB hd⟩ : ↥B) ∈ π.ker := by rw [hπk]; exact hd
    have hc := (π.normal_ker).conj_mem ⟨d, hDB hd⟩ hd' ⟨g, hg⟩
    rw [hπk] at hc
    simpa using (Subgroup.mem_subgroupOf.mp hc)
  have hBN : B ≤ normalizer (D : Set K) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro d
    exact ⟨fun hd => hDnormB g hg d hd, fun hd => by
      have h := hDnormB g⁻¹ (B.inv_mem hg) (g * d * g⁻¹) hd
      simpa [mul_assoc] using h⟩
  refine le_antisymm ?_ hBN
  intro g hg
  have hgd : g * d₀ * g⁻¹ ∈ D :=
    ((Subgroup.mem_normalizer_iff.mp hg) d₀).mp hd₀D
  have hgd1 : g * d₀ * g⁻¹ ≠ 1 := by
    intro h
    apply hd₀1
    calc d₀ = g⁻¹ * (g * d₀ * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨b, hbB, hbconj⟩ := hTrans d₀ hd₀D (g * d₀ * g⁻¹) hgd hd₀1 hgd1
  have hcomm : (b⁻¹ * g) * d₀ * (b⁻¹ * g)⁻¹ = d₀ := by
    calc (b⁻¹ * g) * d₀ * (b⁻¹ * g)⁻¹
        = b⁻¹ * (g * d₀ * g⁻¹) * b := by group
      _ = b⁻¹ * (b * d₀ * b⁻¹) * b := by rw [hbconj]
      _ = d₀ := by group
  have hcent : b⁻¹ * g ∈ centralizer ({d₀} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (b⁻¹ * g) * d₀ = ((b⁻¹ * g) * d₀ * (b⁻¹ * g)⁻¹) * (b⁻¹ * g) := by group
      _ = d₀ * (b⁻¹ * g) := by rw [hcomm]
  have hbcent := hCent d₀ hd₀D hd₀1 hcent
  rw [show g = b * (b⁻¹ * g) from by group]
  exact B.mul_mem hbB hbcent

private theorem exists_sylow_isT_of_e16_alt5
    (hDB : D ≤ B) (hD : IsElemAbelian 2 D) (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥B →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b)
    (hodd : Odd B.index) :
    ∃ T : Sylow 2 K, CFSG.OddStandard.ThmC.T.IsT ↥T ∧ D ≤ T := by
  obtain ⟨π, hπs, hπk⟩ := hπ
  have hk16 : Nat.card ↥π.ker = 16 := by
    rw [hπk]
    calc Nat.card ↥(D.subgroupOf B) = Nat.card ↥D :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
      _ = 16 := hD16
  have hπel : IsElemAbelian 2 π.ker := by rw [hπk]; exact hD.subgroupOf B
  have htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 →
      ∃ g : ↥B, g * a * g⁻¹ = b := by
    intro a ha b hb ha1 hb1
    rw [hπk] at ha hb
    obtain ⟨g, hg, hgab⟩ :=
      hTrans a ha b hb (fun h => ha1 (Subtype.ext h)) (fun h => hb1 (Subtype.ext h))
    exact ⟨⟨g, hg⟩, Subtype.ext hgab⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥B)
  obtain ⟨eP⟩ :=
    CFSG.GH74.PartII.nonempty_mulEquiv_sylSL3_4_of_e16_alt5 hπs hπel hk16 htr P
  let T₀ : Subgroup K := Subgroup.map B.subtype (P : Subgroup ↥B)
  have hT₀p : IsPGroup 2 ↥T₀ := P.isPGroup'.map B.subtype
  have hT₀idx : ¬ 2 ∣ T₀.index := by
    have h := Subgroup.index_map_of_injective (P : Subgroup ↥B) B.subtype_injective
    change ¬ 2 ∣ (Subgroup.map B.subtype (P : Subgroup ↥B)).index
    rw [h, B.range_subtype]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h1 | h1
    · exact Sylow.not_dvd_index P h1
    · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)
  let T : Sylow 2 K := hT₀p.toSylow hT₀idx
  have hDT : D ≤ T := by
    have hDsubnorm : (D.subgroupOf B).Normal := by rw [← hπk]; exact π.normal_ker
    have hDsubp : IsPGroup 2 ↥(D.subgroupOf B) := hD.isPGroup.comap_subtype
    have hle : D.subgroupOf B ≤ (P : Subgroup ↥B) :=
      @IsPGroup.le_sylow_of_normal 2 _ _ (D.subgroupOf B) hDsubnorm hDsubp P
    have hmap := Subgroup.map_mono (f := B.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hDB] at hmap
    rwa [IsPGroup.toSylow_coe hT₀p hT₀idx]
  refine ⟨T, ?_, hDT⟩
  exact ⟨(MulEquiv.subgroupCongr (IsPGroup.toSylow_coe hT₀p hT₀idx)).trans
    ((Subgroup.equivMapOfInjective (P : Subgroup ↥B) B.subtype B.subtype_injective).symm.trans
      eP)⟩

omit [Finite K] in
private theorem exists_isTwoE16_of_isT {T : Sylow 2 K}
    (hT : CFSG.OddStandard.ThmC.T.IsT ↥T) {D : Subgroup K} (hDT : D ≤ T)
    (hD : IsElemAbelian 2 D) (hD16 : Nat.card D = 16) :
    ∃ F : Subgroup K, F ≤ T ∧
      CFSG.OddStandard.ThmC.T.IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T) := by
  obtain ⟨A, B', hAB⟩ := hT.exists_twoE16
  have hDsub_ea : IsElemAbelian 2 (D.subgroupOf T) := hD.subgroupOf T
  have hDsub_sq : ∀ x ∈ D.subgroupOf T, x * x = 1 := by
    intro x hx
    simpa [pow_two] using hDsub_ea.2 x hx
  have hDsub_card : Nat.card ↥(D.subgroupOf T) = 16 := by
    calc Nat.card ↥(D.subgroupOf T) = Nat.card ↥D :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDT).toEquiv
      _ = 16 := hD16
  rcases hAB.eq_or (D.subgroupOf T) hDsub_sq hDsub_card with h | h
  · have hsub : (B'.map (T : Subgroup K).subtype).subgroupOf T = B' :=
      Subgroup.comap_map_eq_self_of_injective (T : Subgroup K).subtype_injective B'
    refine ⟨B'.map (T : Subgroup K).subtype, Subgroup.map_subtype_le _, ?_⟩
    rw [h, hsub]
    exact hAB
  · have hsub : (A.map (T : Subgroup K).subtype).subgroupOf T = A :=
      Subgroup.comap_map_eq_self_of_injective (T : Subgroup K).subtype_injective A
    refine ⟨A.map (T : Subgroup K).subtype, Subgroup.map_subtype_le _, ?_⟩
    rw [h, hsub]
    exact isTwoE16_swap hAB

omit [Finite K] in
private theorem config_eq_or_eq {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hFT : F ≤ T)
    (hDF : CFSG.OddStandard.ThmC.T.IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) :
    ∀ E : Subgroup K, E ≤ T → IsElemAbelian 2 E → Nat.card E = 16 → E = D ∨ E = F := by
  intro E hET hE hE16
  have hEsub : IsElemAbelian 2 (E.subgroupOf T) := hE.subgroupOf T
  have hEsub_sq : ∀ x ∈ E.subgroupOf T, x * x = 1 := by
    intro x hx
    simpa [pow_two] using hEsub.2 x hx
  have hEsub_card : Nat.card ↥(E.subgroupOf T) = 16 := by
    calc Nat.card ↥(E.subgroupOf T) = Nat.card ↥E :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv
      _ = 16 := hE16
  rcases hDF.eq_or (E.subgroupOf T) hEsub_sq hEsub_card with h | h
  · left
    have hmap := congrArg (Subgroup.map (T : Subgroup K).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hET, Subgroup.map_subgroupOf_eq_of_le hDT] at hmap
  · right
    have hmap := congrArg (Subgroup.map (T : Subgroup K).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hET, Subgroup.map_subgroupOf_eq_of_le hFT] at hmap

omit [Finite K] in
private theorem config_card_inf {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hDF : CFSG.OddStandard.ThmC.T.IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) :
    Nat.card ↥(D ⊓ F) = 4 := by
  have hsub : (D ⊓ F).subgroupOf T = D.subgroupOf T ⊓ F.subgroupOf T := rfl
  calc Nat.card ↥(D ⊓ F) = Nat.card ↥((D ⊓ F).subgroupOf T) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hDT)).toEquiv).symm
    _ = Nat.card ↥(D.subgroupOf T ⊓ F.subgroupOf T) := by rw [hsub]
    _ = Nat.card ↥(Subgroup.center ↥T) := by
        rw [hDF.inf_eq]
        rfl
    _ = 4 := hDF.card_center

omit [Finite K] in
private theorem config_inf_le_centralizer {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hDF : CFSG.OddStandard.ThmC.T.IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) :
    D ⊓ F ≤ Subgroup.centralizer (T : Set K) := by
  intro x hx
  have hxT : x ∈ T := hDT hx.1
  have hxsub : (⟨x, hxT⟩ : ↥T) ∈ D.subgroupOf T ⊓ F.subgroupOf T :=
    Subgroup.mem_inf.mpr ⟨hx.1, hx.2⟩
  rw [hDF.inf_eq] at hxsub
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxsub ⟨y, hy⟩)

omit [Finite K] in
private theorem config_mul_self_mem {T : Sylow 2 K} {D F : Subgroup K}
    (hT : CFSG.OddStandard.ThmC.T.IsT ↥T)
    (hDF : CFSG.OddStandard.ThmC.T.IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) :
    ∀ x ∈ T, x * x ∈ D ⊓ F := by
  intro x hx
  have hxT : (⟨x, hx⟩ : ↥T) * ⟨x, hx⟩ ∈ Subgroup.center ↥T := hT.sq_mem_center ⟨x, hx⟩
  rw [← hDF.inf_eq] at hxT
  exact ⟨Subgroup.mem_subgroupOf.mp hxT.1, Subgroup.mem_subgroupOf.mp hxT.2⟩

omit [Finite K] in
private theorem config_mem_or_mem {T : Sylow 2 K} {D F : Subgroup K}
    (hDF : CFSG.OddStandard.ThmC.T.IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) :
    ∀ x ∈ T, x * x = 1 → x ∈ D ∨ x ∈ F := by
  intro x hx hx2
  have hx' : (⟨x, hx⟩ : ↥T) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
  rcases (hDF.sq_iff ⟨x, hx⟩).mp hx' with h | h
  · exact Or.inl (Subgroup.mem_subgroupOf.mp h)
  · exact Or.inr (Subgroup.mem_subgroupOf.mp h)

omit [Finite K] in
private theorem config_centralizer_L {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hDF : CFSG.OddStandard.ThmC.T.IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) :
    ∀ x ∈ D, x ∉ D ⊓ F → Subgroup.centralizer ({x} : Set K) ⊓ T = D := by
  intro x hxD hxZ
  have hxT : x ∈ T := hDT hxD
  have hxnotcenter : (⟨x, hxT⟩ : ↥T) ∉ Subgroup.center ↥T := by
    intro h
    rw [← hDF.inf_eq] at h
    exact hxZ (Subgroup.mem_inf.mpr ⟨h.1, h.2⟩)
  have hsub : (Subgroup.centralizer ({x} : Set K)).subgroupOf T =
      Subgroup.centralizer ({(⟨x, hxT⟩ : ↥T)} : Set ↥T) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [← inf_eq_left.mpr hDT, ← Subgroup.subgroupOf_inj, hsub,
    hDF.centralizer_left ⟨x, hxT⟩ hxD hxnotcenter]

private theorem config_centralizer_L_le {T : Sylow 2 K} {D F : Subgroup K}
    (hT : CFSG.OddStandard.ThmC.T.IsT ↥T) (hD : IsElemAbelian 2 D)
    (hD16 : Nat.card D = 16) (hDT : D ≤ T)
    (hDF : CFSG.OddStandard.ThmC.T.IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (Subgroup.centralizer ({v} : Set K)) = 64) :
    Subgroup.centralizer (D : Set K) ≤ D := by
  have hcardZ : Nat.card ↥(D ⊓ F) = 4 := config_card_inf hDT hDF
  have hneZ : D ⊓ F ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardZ
    omega
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hneZ
  have hzD : (z : K) ∈ D := (Subgroup.mem_inf.mp z.2).1
  have hzF : (z : K) ∈ F := (Subgroup.mem_inf.mp z.2).2
  have hz1 : (z : K) ≠ 1 := fun h => hz (Subtype.ext h)
  have hz2 : orderOf (z : K) = 2 := by
    have h := hD.2 (z : K) hzD
    exact CFSG.OddStandard.ThmC.T.orderOf_eq_two_iff_sq.mpr
      ⟨by simpa [pow_two] using h, hz1⟩
  have hCz : Nat.card (Subgroup.centralizer ({(z : K)} : Set K)) = 64 := hcent (z : K) hz2
  have hzT : (z : K) ∈ T := hDT hzD
  have hzcenter : (⟨z, hzT⟩ : ↥T) ∈ Subgroup.center ↥T := by
    rw [← hDF.inf_eq]
    exact Subgroup.mem_inf.mpr ⟨hzD, hzF⟩
  have hTleCz : T ≤ Subgroup.centralizer ({(z : K)} : Set K) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter ⟨y, hy⟩)
  have hCzT : Subgroup.centralizer ({(z : K)} : Set K) = T :=
    (Subgroup.eq_of_le_of_card_ge hTleCz (by
      rw [show Nat.card ↥(T : Subgroup K) = 64 from hT.card_eq, hCz])).symm
  have hnotDleZ : ¬ D ≤ D ⊓ F := by
    intro hle
    have hc : Nat.card D = Nat.card ↥(D ⊓ F) :=
      Nat.card_congr (MulEquiv.subgroupCongr (le_antisymm hle inf_le_left))
    rw [hD16, hcardZ] at hc
    omega
  obtain ⟨x, hxD, hxZ⟩ := SetLike.not_le_iff_exists.mp hnotDleZ
  have hCx : Subgroup.centralizer ({x} : Set K) ⊓ T = D :=
    config_centralizer_L hDT hDF x hxD hxZ
  intro c hc
  have hcCz : c ∈ Subgroup.centralizer ({(z : K)} : Set K) :=
    Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hzD) hc
  have hcT : c ∈ (T : Subgroup K) := by rw [← hCzT]; exact hcCz
  have hcx : c ∈ Subgroup.centralizer ({x} : Set K) :=
    Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hxD) hc
  have hmem : c ∈ Subgroup.centralizer ({x} : Set K) ⊓ T := ⟨hcx, hcT⟩
  rwa [hCx] at hmem

omit [Finite K] in
private theorem exists_quot_of_normalizer_eq
    (hN : normalizer (D : Set K) = B)
    (hπ : ∃ π : ↥B →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = D.subgroupOf B) :
    ∃ π' : ↥(normalizer (D : Set K)) →* alternatingGroup (Fin 5),
      Function.Surjective π' ∧
        π'.ker = D.subgroupOf (normalizer (D : Set K)) := by
  obtain ⟨π, hπs, hπk⟩ := hπ
  refine ⟨π.comp (MulEquiv.subgroupCongr hN).toMonoidHom,
    hπs.comp (MulEquiv.subgroupCongr hN).surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπk,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  change ↑((MulEquiv.subgroupCongr hN) x) ∈ D ↔ ↑x ∈ D
  rw [MulEquiv.subgroupCongr_apply]

omit [Finite K] in
private theorem exists_conj_of_normalizer_eq
    (hN : normalizer (D : Set K) = B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b) :
    ∀ x ∈ D, ∀ y ∈ D, x ≠ 1 → y ≠ 1 →
      ∃ k ∈ normalizer (D : Set K), k * x * k⁻¹ = y := by
  intro x hx y hy hx1 hy1
  obtain ⟨g, hg, hgxy⟩ := hTrans x hx y hy hx1 hy1
  exact ⟨g, hN.symm ▸ hg, hgxy⟩

omit [Finite K] in
private theorem exists_fpf_of_quot {H : Subgroup K}
    (hπ : ∃ π : ↥(normalizer (H : Set K)) →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = H.subgroupOf (normalizer (H : Set K)))
    (hH : IsElemAbelian 2 H)
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (centralizer ({v} : Set K)) = 64) :
    ∃ f ∈ normalizer (H : Set K), ∀ l ∈ H, f * l = l * f → l = 1 := by
  obtain ⟨π, hπs, hπk⟩ := hπ
  have hπel : IsElemAbelian 2 π.ker := by rw [hπk]; exact hH.subgroupOf _
  obtain ⟨f, hfπ, hf3⟩ := CFSG.GH74.PartII.exists_pow_three_eq_one_of_e16_alt5 hπs hπel
  have hf1 : f ≠ 1 := by
    intro h
    exact CFSG.GH74.PartII.cycle012A5_ne_one (by rw [← hfπ, h, map_one])
  have hford : orderOf f = 3 := orderOf_eq_prime hf3 hf1
  refine ⟨(f : K), f.2, ?_⟩
  intro l hl hcomm
  by_contra hl1
  have hl2 : orderOf l = 2 := by
    have h := hH.2 l hl
    exact CFSG.OddStandard.ThmC.T.orderOf_eq_two_iff_sq.mpr
      ⟨by simpa [pow_two] using h, hl1⟩
  have hmem : (f : K) ∈ Subgroup.centralizer ({l} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have h3dvd : 3 ∣ Nat.card (Subgroup.centralizer ({l} : Set K)) := by
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [Subgroup.orderOf_coe, hford] at h
  rw [hcent l hl2] at h3dvd
  omega

omit [Finite K] in
private theorem isPGroup_centralizer_of_card
    (hcent : ∀ v : K, orderOf v = 2 →
      Nat.card (Subgroup.centralizer ({v} : Set K)) = 64) :
    ∀ e : K, e * e = 1 → e ≠ 1 →
      IsPGroup 2 (Subgroup.centralizer ({e} : Set K)) := by
  intro e he he1
  have hord : orderOf e = 2 :=
    CFSG.OddStandard.ThmC.T.orderOf_eq_two_iff_sq.mpr ⟨he, he1⟩
  have hcard := hcent e hord
  exact IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)

private theorem exists_config_of_sylow_data {T : Sylow 2 K} {D F : Subgroup K}
    (hT : CFSG.OddStandard.ThmC.T.IsT ↥T) (hD : IsElemAbelian 2 D)
    (hD16 : Nat.card D = 16) (hDT : D ≤ T) (hFT : F ≤ T)
    (hDF : CFSG.OddStandard.ThmC.T.IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hcent : ∀ v : K, orderOf v = 2 →
      Nat.card (Subgroup.centralizer ({v} : Set K)) = 64)
    (hπL : ∃ π : ↥(normalizer (D : Set K)) →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = D.subgroupOf (normalizer (D : Set K)))
    (hTransL : ∀ x ∈ D, ∀ y ∈ D, x ≠ 1 → y ≠ 1 →
      ∃ k ∈ normalizer (D : Set K), k * x * k⁻¹ = y)
    (hπM : ∃ π : ↥(normalizer (F : Set K)) →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = F.subgroupOf (normalizer (F : Set K)))
    (hTransM : ∀ x ∈ F, ∀ y ∈ F, x ≠ 1 → y ≠ 1 →
      ∃ k ∈ normalizer (F : Set K), k * x * k⁻¹ = y) :
    ∃ C : CFSG.Quasithin.L34CIT.Config K, C.L = D := by
  have hFsub_ea : IsElemAbelian 2 (F.subgroupOf T) :=
    ⟨⟨⟨fun x y => Subtype.ext (hDF.comm_right x x.2 y y.2)⟩⟩, fun x hx => by
      have h := hDF.sq_right x hx
      simpa [pow_two] using h⟩
  have hF : IsElemAbelian 2 F := by
    have h := hFsub_ea.map (T : Subgroup K).subtype
    rwa [Subgroup.map_subgroupOf_eq_of_le hFT] at h
  have hF16 : Nat.card F = 16 := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hFT,
      Subgroup.card_map_of_injective (T : Subgroup K).subtype_injective]
    exact hDF.card_right
  obtain ⟨πL, hπLs, hπLk⟩ := hπL
  obtain ⟨πM, hπMs, hπMk⟩ := hπM
  let C : CFSG.Quasithin.L34CIT.Config K :=
    { T := T
      L := D
      M := F
      card_T := show Nat.card ↥(T : Subgroup K) = 64 from hT.card_eq
      L_le := hDT
      M_le := hFT
      isElemAbelian_L := hD
      isElemAbelian_M := hF
      card_L := hD16
      card_M := hF16
      eq_or_eq := fun E hE hEea hEcard => config_eq_or_eq hDT hFT hDF E hE hEea hEcard
      card_inf := config_card_inf hDT hDF
      inf_le_centralizer := config_inf_le_centralizer hDT hDF
      mul_self_mem := config_mul_self_mem hT hDF
      mem_or_mem := config_mem_or_mem hDF
      centralizer_L := fun x hx hxZ => config_centralizer_L hDT hDF x hx hxZ
      centralizer_M := fun y hy hyZ =>
        config_centralizer_L hFT (isTwoE16_swap hDF) y hy (by rwa [inf_comm])
      isPGroup_centralizer := isPGroup_centralizer_of_card hcent
      centralizer_L_le := config_centralizer_L_le hT hD hD16 hDT hDF hcent
      centralizer_M_le := config_centralizer_L_le hT hF hF16 hFT (isTwoE16_swap hDF) hcent
      quotL := πL
      quotL_surjective := hπLs
      ker_quotL := hπLk
      quotM := πM
      quotM_surjective := hπMs
      ker_quotM := hπMk
      exists_conj_L := hTransL
      exists_conj_M := hTransM
      exists_fpf_L := exists_fpf_of_quot ⟨πL, hπLs, hπLk⟩ hD hcent
      exists_fpf_M := exists_fpf_of_quot ⟨πM, hπMs, hπMk⟩ hF hcent }
  exact ⟨C, rfl⟩

private theorem card_centralizer_eq_sixtyFour_of_orderOf_eq_two
    (hDB : D ≤ B) (hD : IsElemAbelian 2 D) (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥B →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → centralizer ({d} : Set K) ≤ B)
    (hinv : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    {v : K} (hv : orderOf v = 2) :
    Nat.card (centralizer ({v} : Set K)) = 64 := by
  obtain ⟨d₀, hd₀D, hd₀1, -⟩ :=
    exists_mem_ne_one_ne_of_two_lt_card (D := D) (by omega) 1
  have hd₀2 : orderOf d₀ = 2 :=
    CFSG.OddStandard.ThmC.T.orderOf_eq_two_iff_sq.mpr
      ⟨by simpa [pow_two] using hD.2 d₀ hd₀D, hd₀1⟩
  rw [CFSG.GroupTheory.card_centralizer_singleton_congr_of_isConj (hinv v d₀ hv hd₀2)]
  exact card_centralizer_eq_sixtyFour_of_mem hDB hD16 hπ hTrans hCent hd₀D hd₀1

theorem exists_config_of_e16_alt5 (hDB : D ≤ B) (hD : IsElemAbelian 2 D)
    (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥B →* alternatingGroup (Fin 5), Function.Surjective π ∧ π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → centralizer ({d} : Set K) ≤ B) (hodd : Odd B.index)
    (hproper : 1 < B.index) :
    ∃ C : CFSG.Quasithin.L34CIT.Config K, C.L = D := by
  have hinv := isConj_of_orderOf_eq_two_of_e16_alt5 hDB hD hD16 hπ hTrans hCent hodd hproper
  have hC64 : ∀ d ∈ D, d ≠ 1 → Nat.card (centralizer ({d} : Set K)) = 64 :=
    fun d hd hd1 => card_centralizer_eq_sixtyFour_of_mem hDB hD16 hπ hTrans hCent hd hd1
  have hN : normalizer (D : Set K) = B :=
    normalizer_eq_of_e16_alt5 hDB hD16 hπ hTrans hCent
  have hcent : ∀ v : K, orderOf v = 2 →
      Nat.card (centralizer ({v} : Set K)) = 64 :=
    fun v hv =>
      card_centralizer_eq_sixtyFour_of_orderOf_eq_two hDB hD hD16 hπ hTrans hCent hinv hv
  have hπL : ∃ π : ↥(normalizer (D : Set K)) →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = D.subgroupOf (normalizer (D : Set K)) :=
    exists_quot_of_normalizer_eq hN hπ
  have hTransL : ∀ x ∈ D, ∀ y ∈ D, x ≠ 1 → y ≠ 1 →
      ∃ k ∈ normalizer (D : Set K), k * x * k⁻¹ = y :=
    exists_conj_of_normalizer_eq hN hTrans
  obtain ⟨T, hT, hDT⟩ := exists_sylow_isT_of_e16_alt5 hDB hD hD16 hπ hTrans hodd
  obtain ⟨F, hFT, hDF⟩ := exists_isTwoE16_of_isT hT hDT hD hD16
  obtain ⟨hπM, hTransM⟩ :=
    exists_alt5_of_normalizer_other_e16 T hT hDT hFT hDF hinv hcent hπL
  exact exists_config_of_sylow_data hT hD hD16 hDT hFT hDF hcent hπL hTransL hπM hTransM

end CFSG.RankThree.GF2n.Parrott
