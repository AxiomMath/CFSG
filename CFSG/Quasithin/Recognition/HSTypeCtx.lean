module

public import CFSG.Quasithin.Recognition.HSType16c
public import CFSG.Quasithin.Recognition.HSType15f
public import CFSG.Quasithin.Recognition.HSType16b

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L34Amalgam MulAction
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open HSSetting

structure HSCtx (G : Type) [Group G] [Finite G] where
  z : G
  V : Subgroup G
  s : G
  M : S6Model z s
  h : HSSetting z V
  hsmemH : s ∈ hsH z
  hsnotK : s ∉ hsK z
  hss : s * s = 1
  g₀ : G
  hg₀ : g₀ * z * g₀⁻¹ = s
  g : G
  hg : g ∈ Subgroup.normalizer (M.V2 : Set G)
  hgNN : g ∉ M.NN
  x : G
  hx3 : orderOf x = 3
  hxRX : x ∈ M.RX
  i : ↥(hsNB z s)
  hi2 : (i : G) * i = 1
  hix : (i : G) * x * (i : G)⁻¹ = x⁻¹
  hist : M.π i ∈ stabS
  hil : M.π i ∉ lamS
  hifx : M.π i ∉ fixS
  hin : NormLamS (M.π i)
  hiz : ∃ c : G, c * z * c⁻¹ = i
  Φ : ↥(M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom) ≃* ↥(stabilizer M22 (0 : Fin 22))
  hΦ1 : ∀ y : ↥(M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom), (y : G) ∈ M.L1 ↔
    ((Φ y : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab
  hΦ2 : ∀ y : ↥(M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom),
    (y : G) ∈ M.L1.map (MulAut.conj g).toMonoidHom ↔
      ((Φ y : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab
  hiNL : (i : G) ∉
    Subgroup.normalizer ((M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
  hiI₀ : (i : G) ∈ (M.pre (alternatingGroup (Fin 6))).map (MulAut.conj g).toMonoidHom
  hiL : (i : G) ∉ M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom
  hLI₀ : ∀ w ∈ M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom,
    w ∈ (M.pre (alternatingGroup (Fin 6))).map (MulAut.conj g).toMonoidHom →
      w ∈ M.L1.map (MulAut.conj g).toMonoidHom
  hLi : ∀ k ∈ M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom,
    (i : G) * k * i ∈ M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom ↔ k ∈ M.L1
  Ψ : ↥((M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom) ⊔
      (M.pre (alternatingGroup (Fin 6))).map (MulAut.conj g).toMonoidHom) ≃* M22
  hΨL : ∀ y : ↥((M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom) ⊔
      (M.pre (alternatingGroup (Fin 6))).map (MulAut.conj g).toMonoidHom),
    (y : G) ∈ M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom ↔ Ψ y ∈ stabilizer M22 (0 : Fin 22)
  hΨI : ∀ y : ↥((M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom) ⊔
      (M.pre (alternatingGroup (Fin 6))).map (MulAut.conj g).toMonoidHom),
    (y : G) ∈ (M.pre (alternatingGroup (Fin 6))).map (MulAut.conj g).toMonoidHom ↔
      Ψ y ∈ m22HexStab

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

abbrev L1 : Subgroup G := C.M.L1

abbrev L2 : Subgroup G := C.M.L1.map (MulAut.conj C.g).toMonoidHom

abbrev L : Subgroup G := C.L1 ⊔ C.L2

abbrev I0 : Subgroup G := (C.M.pre (alternatingGroup (Fin 6))).map (MulAut.conj C.g).toMonoidHom

abbrev J : Subgroup G := C.L ⊔ C.I0

end HSCtx

theorem exists_hsCtx
    (hfact : FactAutL34) {G : Type} [Group G] [Finite G] (hG : IsTypeHS G) :
    Nonempty (HSCtx G) := by
  obtain ⟨z, V, hz, hV, hV8, h1, h2⟩ := hG
  have h : HSSetting z V := ⟨hz, hV, hV8, h1, h2⟩
  obtain ⟨s, ⟨hsmemH, -⟩, hss, hsinv, g₀, hg₀⟩ := h.exists_invol_inverts_ZQ
  have hsnotK := h.not_mem_K_of_inverts hsinv
  obtain ⟨M⟩ := nonempty_s6Model h hsmemH hsnotK hss hg₀
  obtain ⟨g₁, hg₁, hg₁NN, Φ₁, hΦ₁₁, hΦ₁₂⟩ := M.exists_mulEquiv_L34 h hsmemH hsnotK hss hg₀
  obtain ⟨x, hx3, hπx, hxRX⟩ := M.exists_x2
  obtain ⟨i, hi2, hix, hist, hil, hifx, hin, c, hc⟩ := M.exists_i h hsmemH hsnotK hss hg₀ hx3 hπx
  obtain ⟨g, hg, hgNN, hmap, hx'N, hπx'⟩ :=
    M.exists_adjust h hsmemH hsnotK hss hg₀ hg₁ hg₁NN hxRX hx3
  set L₂ := M.L1.map (MulAut.conj g).toMonoidHom with hL₂
  set L := M.L1 ⊔ L₂ with hL
  set I₀ := (M.pre (alternatingGroup (Fin 6))).map (MulAut.conj g).toMonoidHom with hI₀
  have hLeq : L = M.L1 ⊔ M.L1.map (MulAut.conj g₁).toMonoidHom := by
    rw [hL, hmap]
  set Φ : ↥L ≃* ↥(stabilizer M22 (0 : Fin 22)) := (MulEquiv.subgroupCongr hLeq).trans Φ₁ with hΦ
  have hΦ1 : ∀ y : ↥L, (y : G) ∈ M.L1 ↔
      ((Φ y : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab := fun y =>
    hΦ₁₁ (MulEquiv.subgroupCongr hLeq y)
  have hΦ2 : ∀ y : ↥L, (y : G) ∈ L₂ ↔
      ((Φ y : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab := fun y => by
    have e : (y : G) ∈ L₂ ↔ (y : G) ∈ M.L1.map (MulAut.conj g₁).toMonoidHom := by rw [hmap]
    exact e.trans (hΦ₁₂ (MulEquiv.subgroupCongr hLeq y))
  have hL1L : M.L1 ≤ L := le_sup_left
  have hL2L : L₂ ≤ L := le_sup_right
  have hiNL := M.not_mem_normalizer_L hfact h hsmemH hsnotK hss hg₀ hL1L Φ hΦ1 hi2 hil hin hc
  obtain ⟨hyN, hyst, hyalt, hyl⟩ := M.mem_alt_conj h hsmemH hsnotK hss hg₀ hg hi2 hist hil hifx
    hin hiNL
  have hii : (i : G)⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hixG : (i : G) * x * (i : G)⁻¹ = (x : G)⁻¹ := hix
  obtain ⟨j, hjL₂, hjL₁, hjj, hij⟩ := M.exists_j_of_i h hsmemH hsnotK hss hg₀ hg hgNN hx3 hx'N
    hπx' hi2 hixG hyN hyst hyalt
  have hiI₀ : (i : G) ∈ I₀ := by
    rw [hI₀, mem_map_conj_iff]
    exact M.mem_pre.mpr ⟨hyN, hyalt⟩
  have hiL₂ : (i : G) ∉ L₂ := by
    intro hm
    rw [hL₂, mem_map_conj_iff] at hm
    exact hyl (M.π_mem_of_mem_pre hm hyN)
  have hL₂I₀ : L₂ ≤ I₀ := Subgroup.map_mono (M.pre_mono lamS_le_alt)
  have hI₀cases : ∀ w ∈ I₀, w ∈ L₂ ∨ ∃ a ∈ L₂, ∃ b ∈ L₂, w = a * i * b := by
    intro w hw
    rw [hI₀, mem_map_conj_iff] at hw
    rcases M.mem_pre_alt_cases (y := ⟨g⁻¹ * i * g, hyN⟩) hyst hyalt hyl hw with
      h1 | ⟨a, ha, b, hb, hab⟩
    · left
      rw [hL₂, mem_map_conj_iff]
      exact h1
    · right
      refine ⟨g * a * g⁻¹, ?_, g * b * g⁻¹, ?_, ?_⟩
      · rw [hL₂, mem_map_conj_iff, show g⁻¹ * (g * a * g⁻¹) * g = a by group]
        exact ha
      · rw [hL₂, mem_map_conj_iff, show g⁻¹ * (g * b * g⁻¹) * g = b by group]
        exact hb
      · calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
          _ = g * (a * (g⁻¹ * i * g) * b) * g⁻¹ := by rw [hab]
          _ = g * a * g⁻¹ * i * (g * b * g⁻¹) := by group
  have hiL : (i : G) ∉ L := fun hm =>
    hil (M.π_mem_of_mem_pre (M.inf_hsNB_le_L1 h hsmemH hsnotK hss hg₀ hg hgNN Φ hΦ1 hm i.2) i.2)
  have hLI₀ : ∀ w ∈ L, w ∈ I₀ → w ∈ L₂ := by
    intro w hwL hwI
    rcases hI₀cases w hwI with h1 | ⟨a, ha, b, hb, hab⟩
    · exact h1
    · exfalso
      apply hiL
      have : (i : G) = a⁻¹ * w * b⁻¹ := by rw [hab]; group
      rw [this]
      exact L.mul_mem (L.mul_mem (L.inv_mem (hL2L ha)) hwL) (L.inv_mem (hL2L hb))
  have hLi : ∀ k ∈ L, (i : G) * k * i ∈ L ↔ k ∈ M.L1 := by
    intro k hk
    constructor
    · intro hik
      by_contra hk1
      apply hiNL
      have hle := le_of_lt_L1 (X := L ⊓ L.comap (MulAut.conj (i : G)).toMonoidHom) Φ hΦ1
        (fun u hu => ⟨hL1L hu, show (i : G) * u * (i : G)⁻¹ ∈ L from
          hL1L (M.conj_mem_L1 hin hu)⟩) hk ⟨hk, show (i : G) * k * (i : G)⁻¹ ∈ L by
            rw [hii]; exact hik⟩ hk1
      exact Subgroup.mem_normalizer_fintype fun u hu => (hle hu).2
    · intro hk1
      have := M.conj_mem_L1 hin hk1
      rw [hii] at this
      exact hL1L this
  set J := L ⊔ I₀ with hJ
  set K := L.subgroupOf J with hK
  set H := I₀.subgroupOf J with hH
  set ΦK : ↥K ≃* ↥(stabilizer M22 (0 : Fin 22)) :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ J)).trans Φ with hΦK
  have hΦK : ∀ k : ↥K, ΦK k = Φ ⟨((k : ↥J) : G), Subgroup.mem_subgroupOf.mp k.2⟩ := fun k => rfl
  have hgen : K ⊔ H = ⊤ := by
    rw [hK, hH, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hHK : ∀ k : ↥K, ((k : ↥J) ∈ H ↔
      ((ΦK k : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab) := by
    intro k
    rw [hΦK, ← hΦ2, hH, Subgroup.mem_subgroupOf]
    exact ⟨fun h1 => hLI₀ _ (Subgroup.mem_subgroupOf.mp k.2) h1, fun h1 => hL₂I₀ h1⟩
  have hcardI₀ : Nat.card I₀ = 5760 := by
    rw [hI₀, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      M.card_pre h hsmemH hsnotK hss hg₀, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have hcardL₂ : Nat.card L₂ = 960 := by
    rw [hL₂, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      M.card_L1 h hsmemH hsnotK hss hg₀]
  have hKH : K ⊓ H = L₂.subgroupOf J := by
    ext y
    rw [Subgroup.mem_inf, hK, hH, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact ⟨fun ⟨h1, h2⟩ => hLI₀ _ h1 h2, fun h1 => ⟨hL2L h1, hL₂I₀ h1⟩⟩
  have hcKH : Nat.card ↥(K ⊓ H) = 960 := by
    rw [hKH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hL2L.trans le_sup_left)).toEquiv,
      hcardL₂]
  have hcH : Nat.card ↥H = 5760 := by
    rw [hH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : I₀ ≤ J)).toEquiv,
      hcardI₀]
  have hH6 : K.relIndex H = 6 := by
    have h1 := Subgroup.relIndex_mul_card (H := K) (K := H)
    rw [hcKH, hcH] at h1
    omega
  set t : ↥J := ⟨i, Subgroup.mem_sup_right hiI₀⟩ with ht
  have htt : t * t = 1 := Subtype.ext hi2
  have htK : ∀ k : ↥K, t * (k : ↥J) * t ∈ K ↔
      ((ΦK k : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab := by
    intro k
    rw [hΦK, ← hΦ1]
    exact Subgroup.mem_subgroupOf.trans (hLi _ (Subgroup.mem_subgroupOf.mp k.2))
  have hHt : ∀ w ∈ H, w ∈ K ∨ ∃ a ∈ H ⊓ K, ∃ b ∈ H ⊓ K, w = a * t * b := by
    intro w hw
    rw [hH, Subgroup.mem_subgroupOf] at hw
    rcases hI₀cases _ hw with h1 | ⟨a, ha, b, hb, hab⟩
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr (hL2L h1))
    · right
      refine ⟨⟨a, Subgroup.mem_sup_left (hL2L ha)⟩, ⟨Subgroup.mem_subgroupOf.mpr (hL₂I₀ ha),
        Subgroup.mem_subgroupOf.mpr (hL2L ha)⟩, ⟨b, Subgroup.mem_sup_left (hL2L hb)⟩,
        ⟨Subgroup.mem_subgroupOf.mpr (hL₂I₀ hb), Subgroup.mem_subgroupOf.mpr (hL2L hb)⟩,
        Subtype.ext hab⟩
  set jJ : ↥J := ⟨j, Subgroup.mem_sup_left (hL2L hjL₂)⟩ with hjJ
  have hjK : jJ ∈ K := Subgroup.mem_subgroupOf.mpr (hL2L hjL₂)
  have hj₁ : ((ΦK ⟨jJ, hjK⟩ : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∉ m22TwoStab := by
    rw [hΦK, ← hΦ1]
    exact hjL₁
  obtain ⟨Ψ, hΨK, hΨH⟩ := M22Witt.nonempty_mulEquiv_m22_of_local ΦK hgen hHK hH6 htt htK hHt hjK
    hj₁ (Subtype.ext hjj) (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact hij))
  exact ⟨{
    z := z, V := V, s := s, M := M, h := h, hsmemH := hsmemH, hsnotK := hsnotK,
    hss := hss, g₀ := g₀, hg₀ := hg₀, g := g, hg := hg, hgNN := hgNN, x := x, hx3 := hx3,
    hxRX := hxRX, i := i, hi2 := hi2, hix := hixG, hist := hist, hil := hil, hifx := hifx,
    hin := hin, hiz := ⟨c, hc⟩, Φ := Φ, hΦ1 := hΦ1, hΦ2 := hΦ2, hiNL := hiNL, hiI₀ := hiI₀,
    hiL := hiL, hLI₀ := hLI₀, hLi := hLi, Ψ := Ψ,
    hΨL := fun y => by
      rw [← hΨK]
      constructor
      · intro hy
        exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      · rintro ⟨y', hy', hyy'⟩
        rw [Ψ.injective hyy'] at hy'
        exact Subgroup.mem_subgroupOf.mp hy',
    hΨI := fun y => by
      rw [← hΨH]
      constructor
      · intro hy
        exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      · rintro ⟨y', hy', hyy'⟩
        rw [Ψ.injective hyy'] at hy'
        exact Subgroup.mem_subgroupOf.mp hy' }⟩

end CFSG.Quasithin.HSType
