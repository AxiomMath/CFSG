module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TN2a
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNLie
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNSz

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H13.L828N
open scoped IsMulCommutative

section N2aMain

variable {G : Type} [Group G] [Finite G]

theorem s828N_case2a_false (hE3 : E3_828) {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (c : S828Ctx T L I H h k)
    (hmin : MinParabolic H T (H ⊓ fsuM T L))
    (hP7 : H ⊓ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hHIT : H = ch82I (fsuV T I) h ⊔ T) {Y : Subgroup G} (hHY : H = Y ⊔ T)
    (hTN : T ≤ Subgroup.normalizer (Y : Set G)) {n : ℕ}
    (hsz : IsSz n ↥(E2.star (H ⊓ fsuM T L) H Y))
    (hD5 : Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup 5)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := fsuV T I with hVdef
  set Ih := ch82I V h with hIhdef
  set M := H ⊓ fsuM T L with hMdef
  have hTH : T ≤ H := hHY ▸ le_sup_right
  have hYH : Y ≤ H := hHY ▸ le_sup_left
  have hVT : V ≤ T := c.hVT
  have hVH : V ≤ H := hVT.trans hTH
  have hIH : Ih ≤ H := hHIT ▸ le_sup_left
  have hTfM : T ≤ fsuM T L := by
    show T ≤ Subgroup.normalizer (fsuL0 T L : Set G)
    rw [c.hL0]
    exact c.hTL
  have hTM : T ≤ M := le_inf hTH hTfM
  have hMH : M ≤ H := inf_le_left
  have hT : QuasithinUnique.IsSylowTwoOf T H := hmin.isSylow
  set J₀ : Subgroup ↥H := (kerIn M H).subgroupOf H with hJ₀
  haveI hJ₀n : J₀.Normal := E2.kerIn_subgroupOf_normal M H
  set φ : ↥H →* ↥H ⧸ J₀ := QuotientGroup.mk' J₀ with hφ
  set Y' : Subgroup ↥H := Y.subgroupOf H with hY'
  set T' : Subgroup ↥H := T.subgroupOf H with hT'
  set Mm : Subgroup ↥H := M.subgroupOf H with hMm
  set V' : Subgroup ↥H := V.subgroupOf H with hV'
  haveI hY'n : Y'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr
      (hHY ▸ sup_le Subgroup.le_normalizer hTN)
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hT2' : IsPGroup 2 ↥T' := hT2.comap_of_injective H.subtype H.subtype_injective
  have hTi : ¬ 2 ∣ T'.index := hT.2.2
  have hTMm : T' ≤ Mm := fun x hx => Subgroup.mem_subgroupOf.mpr (hTM (Subgroup.mem_subgroupOf.mp hx))
  have hJM : J₀ ≤ Mm := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (kerIn_le (Subgroup.mem_subgroupOf.mp hx))
  have hcore : ∀ N : Subgroup ↥H, N.Normal → N ≤ Mm → N ≤ J₀ := by
    intro N hN hNM x hx
    rw [hJ₀, Subgroup.mem_subgroupOf, mem_kerIn]
    intro b hb
    have h1 := hN.conj_mem x hx ⟨b, hb⟩
    exact Subgroup.mem_subgroupOf.mp (hNM h1)
  have hsup : Y' ⊔ T' = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYH,
      Subgroup.map_subgroupOf_eq_of_le hTH, ← hHY, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfac : ∀ g : ↥H, ∃ y ∈ Y', ∃ t ∈ T', g = y * t := by
    intro g
    have hg : g ∈ Y' ⊔ T' := by rw [hsup]; exact Subgroup.mem_top g
    obtain ⟨y, hy, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    exact ⟨y, hy, t, ht, rfl⟩
  have hsz' : IsSz n ↥(Y'.map φ) := hsz
  have hn2 : 2 ≤ n := by
    obtain ⟨-, a, ha, -, -, -, hf, -, -⟩ := hsz
    omega
  obtain ⟨hsimp, hnonab⟩ := e22Simple_simple (X := ↥(Y'.map φ)) (Or.inl ⟨n, hn2, Or.inr hsz'⟩)
  have hZ0 : ∀ x ∈ Y'.map φ, (∀ y ∈ Y'.map φ, x * y = y * x) → x = 1 :=
    s828N_center_bot_sub hsimp hnonab
  have hC : ∀ x : ↥H ⧸ J₀, (∀ y ∈ Y'.map φ, x * y = y * x) → x = 1 :=
    img_centralizer_eq_bot J₀ hT2' hTi hTMm hJM hcore hfac hZ0
  have hMax : ∀ B : Subgroup ↥H, T' ≤ B → B ≠ ⊤ → B ≤ Mm := by
    intro B hTB hBt
    have hB1 : B.map H.subtype ≤ H := Subgroup.map_subtype_le B
    have hT1 : T ≤ B.map H.subtype := by
      have := Subgroup.map_mono (f := H.subtype) hTB
      rwa [hT', Subgroup.map_subgroupOf_eq_of_le hTH] at this
    have hlt : B.map H.subtype < H := by
      refine lt_of_le_of_ne hB1 fun heq => hBt ?_
      apply Subgroup.map_injective H.subtype_injective
      rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have := s828N_uniqueMax_le hmin.uniqueMax hT1 hlt
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (this (Subgroup.mem_map_of_mem H.subtype hx))
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact c.hV.2 _ x.2)⟩
  have hV1' : ¬ V' ≤ J₀ := by
    intro hle
    apply s828N_not_le_kerIn hP7 hV2 hVH c.hC.1
    intro v hv
    have hvV' : (⟨v, hVH hv⟩ : ↥H) ∈ V' := hv
    exact Subgroup.mem_subgroupOf.mp (hle hvV')
  have hV2' : CFSG.Open.IsElemAbelian 2 V' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have h1 := mul_comm (⟨((a : ↥H) : G), a.2⟩ : ↥V) ⟨((b : ↥H) : G), b.2⟩
      exact congrArg (fun z : ↥V => (z : G)) h1
    · apply Subtype.ext
      have h1 := c.hV.2 ((x : ↥H) : G) hx
      simpa using h1
  have hVM : ∀ m ∈ Mm.map φ, ∀ v ∈ V'.map φ, m * v * m⁻¹ ∈ V'.map φ := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨m * v * m⁻¹, ?_, by simp⟩
    show m * v * m⁻¹ ∈ V'
    rw [hV', Subgroup.mem_subgroupOf]
    have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    have := (Subgroup.mem_normalizer_iff.mp (hP7 hmM) (v : G)).mp hvV
    simpa using this
  set P : Subgroup G := pCoreOf 2 Ih with hP
  have hPIh : P ≤ Ih := CFSG.LieType.BorelTits.pCoreOf_le 2 Ih
  have hkerI : kerIn (fsuM T L ⊓ Ih) Ih = P := by
    obtain ⟨-, -, -, -, -, -, -, hkerI, -⟩ := id c.hC
    exact hkerI
  set I' : Subgroup ↥H := Ih.subgroupOf H with hI'
  set P' : Subgroup ↥H := P.subgroupOf H with hP'
  have hPI' : P' ≤ I' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hPIh (Subgroup.mem_subgroupOf.mp hx))
  have hVI' : V' ≤ I' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ((le_sup_left : V ≤ Ih) (Subgroup.mem_subgroupOf.mp hx))
  have hVT' : V' ≤ T' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hVT (Subgroup.mem_subgroupOf.mp hx))
  haveI hPn : (P.subgroupOf Ih).Normal := by
    rw [hP, CFSG.openPCoreOf_subgroupOf]
    infer_instance
  haveI hP'n : (P'.subgroupOf I').Normal := by
    constructor
    intro x hx g
    have hx1 : (((x : ↥I') : ↥H) : G) ∈ P := by
      have := Subgroup.mem_subgroupOf.mp hx
      exact Subgroup.mem_subgroupOf.mp this
    have hxIh : (((x : ↥I') : ↥H) : G) ∈ Ih := Subgroup.mem_subgroupOf.mp x.2
    have hgIh : (((g : ↥I') : ↥H) : G) ∈ Ih := Subgroup.mem_subgroupOf.mp g.2
    have h2 := hPn.conj_mem ⟨(((x : ↥I') : ↥H) : G), hxIh⟩ (Subgroup.mem_subgroupOf.mpr hx1)
      ⟨(((g : ↥I') : ↥H) : G), hgIh⟩
    have h3 := Subgroup.mem_subgroupOf.mp h2
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using h3))
  have hP2' : IsPGroup 2 ↥P' :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Ih).comap_of_injective H.subtype H.subtype_injective
  have hJ : ∀ x ∈ I', x ∈ J₀ → x ∈ P' := by
    intro x hxI hxJ
    rw [hP', Subgroup.mem_subgroupOf, ← hkerI, mem_kerIn]
    intro b hb
    have hxk : (x : G) ∈ kerIn M H := Subgroup.mem_subgroupOf.mp hxJ
    have hxI' : (x : G) ∈ Ih := Subgroup.mem_subgroupOf.mp hxI
    exact ⟨((mem_kerIn.mp hxk) b (hIH hb)).2, Ih.mul_mem (Ih.mul_mem hb hxI') (Ih.inv_mem hb)⟩
  obtain ⟨eD⟩ := hD5
  haveI : ((kerIn (fsuM T L ⊓ Ih) Ih).subgroupOf Ih).Normal :=
    E2.kerIn_subgroupOf_normal (fsuM T L ⊓ Ih) Ih
  have e1 : ↥Ih ⧸ P.subgroupOf Ih ≃* DihedralGroup 5 :=
    (QuotientGroup.quotientMulEquivOfEq (by rw [hkerI])).symm.trans eD
  obtain ⟨eI'⟩ := s828N_subgroupOf_quot_equiv hIH hPIh e1
  haveI hIPn := img_subgroupOf_normal J₀ hPI'
  obtain ⟨eIimg⟩ := img_dihedral J₀ hPI' hJ eI'
  haveI : (Y'.map φ).Normal := img_normal J₀
  exact s828N_szEnd hE3 (Y'.map φ) hsz' hC (T'.map φ) (img_isPGroup J₀ hT2')
    (img_index_odd J₀ hTi) (img_factor J₀ hfac) (Mm.map φ) (Subgroup.map_mono hTMm)
    (img_unique_max J₀ hJM hMax) (V'.map φ) (Subgroup.map_mono hVT') (img_elemAbelian J₀ hV2')
    hVM (img_ne_bot J₀ hV1') (I'.map φ) (P'.map φ) (Subgroup.map_mono hVI')
    (Subgroup.map_mono hPI') (img_isPGroup J₀ hP2') eIimg

end N2aMain

end CFSG.Quasithin.H13
