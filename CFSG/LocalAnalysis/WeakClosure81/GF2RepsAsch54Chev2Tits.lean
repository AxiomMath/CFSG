module

import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTits
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2OrbitFrame
import CFSG.Quasithin.Background.GoldschmidtShultLink
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Cat
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.TitsStab
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoAssembly

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

private theorem twoParLat_map {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    {T P₁ P₂ : Subgroup S} (h : TwoParLat S T P₁ P₂) :
    TwoParLat S' (T.map e.toMonoidHom) (P₁.map e.toMonoidHom) (P₂.map e.toMonoidHom) := by
  set φ : Subgroup S ≃o Subgroup S' := e.mapSubgroup with hφ
  have hφa : ∀ X : Subgroup S, φ X = X.map e.toMonoidHom := fun X => rfl
  have hpe : ∀ P : Subgroup S,
      pElementSubgroup 2 (φ P) = φ (pElementSubgroup 2 P) :=
    fun P => pElementSubgroup_map_equiv e P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isSylowTwoOf_top_map_equiv e h.sylow
  · rw [← Subgroup.map_equiv_normalizer_eq T e, h.normT]
  · exact φ.lt_iff_lt.2 h.lt₁
  · exact φ.lt_iff_lt.2 h.lt₂
  · intro Q' hQ1 hQ2
    obtain ⟨Q, rfl⟩ := φ.surjective Q'
    rcases h.atom₁ Q (φ.le_iff_le.1 hQ1) (φ.le_iff_le.1 hQ2) with e1 | e1
    · exact Or.inl (by rw [e1]; exact hφa T)
    · exact Or.inr (by rw [e1]; exact hφa P₁)
  · intro Q' hQ1 hQ2
    obtain ⟨Q, rfl⟩ := φ.surjective Q'
    rcases h.atom₂ Q (φ.le_iff_le.1 hQ1) (φ.le_iff_le.1 hQ2) with e1 | e1
    · exact Or.inl (by simpa [e1] using hφa T)
    · exact Or.inr (by simpa [e1] using hφa P₂)
  · exact fun e1 => h.ne (φ.injective (by simpa [hφa] using e1))
  · intro e1
    exact h.top₁ (φ.injective (by
      rw [hφa P₁, e1]
      exact (φ.map_top).symm))
  · intro e1
    exact h.top₂ (φ.injective (by
      rw [hφa P₂, e1]
      exact (φ.map_top).symm))
  · intro Y' hY
    obtain ⟨Y, rfl⟩ := φ.surjective Y'
    rcases h.hover Y (φ.le_iff_le.1 hY) with e1 | e1 | e1 | e1
    · exact Or.inl (by simpa [e1] using hφa T)
    · exact Or.inr (Or.inl (by simpa [e1] using hφa P₁))
    · exact Or.inr (Or.inr (Or.inl (by simpa [e1] using hφa P₂)))
    · exact Or.inr (Or.inr (Or.inr (by simp [e1])))
  · rw [← hφa P₁, hpe]
    exact φ.le_iff_le.2 h.gen₁
  · rw [← hφa P₂, hpe]
    exact φ.le_iff_le.2 h.gen₂
  · exact CFSG.QuasithinUnique.Ch1.charTwo_map_mulEquiv e h.ct₁
  · exact CFSG.QuasithinUnique.Ch1.charTwo_map_mulEquiv e h.ct₂

theorem false_of_uniqueMax_tits
    {Q : Type} [Group Q] [Finite Q] {L T M : Subgroup Q} (hLn : L.Normal)
    (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) {n f : ℕ}
    (hm : CFSG.Models.LieModel ↥L .Tits n 2 f) (hT : IsSylowIn 2 T ⊤) (hMt : M < ⊤)
    (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M) : False := by
  classical
  let hLnorm : L.Normal := hLn
  obtain ⟨-, hcl | ⟨-, d, hnames, ⟨e⟩⟩⟩ := hm
  · exact hcl.2.elim
  · obtain ⟨⟨idx, hv⟩, rfl⟩ :
        ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
    have hidx : idx = .tits := by
      cases idx <;> simp_all only [CFSG.Models.NamesTag]
    subst hidx
    obtain ⟨eCat⟩ :=
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.nonempty_mulEquiv_titsD_cat hv
    have eL : ↥L ≃* ↥titsD := e.trans eCat
    let S : Subgroup Q := T ⊓ L
    let S_L : Subgroup ↥L := S.subgroupOf L
    have hT' : IsSylowTwoOf T ⊤ := ⟨hT.1, hT.2.1, hT.2.2⟩
    have hS : IsSylowTwoOf S L :=
      CFSG.Quasithin.Shult.isSylowTwoOf_inf_normal (L := L) hT'
    have hSL : IsSylowTwoOf S_L ⊤ := by
      refine ⟨le_top, hS.2.1.comap_subtype, ?_⟩
      have hidx : (S_L.subgroupOf ⊤).index = S_L.index :=
        Subgroup.relIndex_top_right S_L
      rw [hidx]
      exact hS.2.2
    let T₀ : Subgroup ↥L := titsFlagStab.map eL.symm.toMonoidHom
    let H₀ : Subgroup ↥L := titsPointStab.map eL.symm.toMonoidHom
    let N₀ : Subgroup ↥L := titsLineStab.map eL.symm.toMonoidHom
    have h0 : TwoParLat ↥L T₀ H₀ N₀ := by
      simpa [T₀, H₀, N₀] using twoParLat_map eL.symm twoParLat_tits
    obtain ⟨g, hg⟩ := exists_conj_of_sylowTwo h0.sylow hSL
    let P₁ : Subgroup ↥L := H₀.map (MulAut.conj g).toMonoidHom
    let P₂ : Subgroup ↥L := N₀.map (MulAut.conj g).toMonoidHom
    have hLat : TwoParLat ↥L S_L P₁ P₂ := by
      have h1 := twoParLat_map (MulAut.conj g) h0
      rw [hg] at h1
      simpa [P₁, P₂] using h1
    have hT₀card : Nat.card T₀ = 2048 := by
      simp only [T₀]
      rw [Subgroup.card_map_of_injective eL.symm.injective,
        CFSG.Sporadic.Schreier.Tits.card_titsFlagStab]
    have hH₀card : Nat.card H₀ = 10240 := by
      simp only [H₀]
      rw [Subgroup.card_map_of_injective eL.symm.injective,
        CFSG.Sporadic.Schreier.Tits.card_titsPointStab]
    have hN₀card : Nat.card N₀ = 6144 := by
      simp only [N₀]
      rw [Subgroup.card_map_of_injective eL.symm.injective,
        CFSG.Sporadic.Schreier.Tits.card_titsLineStab]
    have hS_card : Nat.card S_L = 2048 := by
      rw [← hg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hT₀card]
    have hP₁card : Nat.card P₁ = 10240 := by
      simp only [P₁]
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hH₀card]
    have hP₂card : Nat.card P₂ = 6144 := by
      simp only [P₂]
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hN₀card]
    have hTnormS : T ≤ Subgroup.normalizer (S : Set Q) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine le_antisymm ?_ ?_
      · rintro x ⟨y, hy, rfl⟩
        exact ⟨T.mul_mem (T.mul_mem ht hy.1) (T.inv_mem ht), hLn.conj_mem y hy.2 t⟩
      · intro x hx
        refine ⟨t⁻¹ * x * t, ⟨?_, ?_⟩, ?_⟩
        · exact T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht
        · simpa using hLn.conj_mem x hx.2 t⁻¹
        · show t * (t⁻¹ * x * t) * t⁻¹ = x
          group
    have hSmap : ∀ t ∈ T, S.map (MulAut.conj t).toMonoidHom = S := fun t ht =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnormS ht)
    have hcomp : ∀ t : Q,
        L.subtype.comp (MulAut.conjNormal (H := L) t).toMonoidHom =
          (MulAut.conj t).toMonoidHom.comp L.subtype := by
      intro t
      ext l
      simp [MulAut.conjNormal_apply]
    have hSL_fixed : ∀ t ∈ T,
        S_L.map (MulAut.conjNormal (H := L) t).toMonoidHom = S_L := by
      intro t ht
      have hSLmap : S_L.map L.subtype = S := by
        simp [S_L, S]
      apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
      calc
        (S_L.map (MulAut.conjNormal (H := L) t).toMonoidHom).map L.subtype
            = S_L.map (L.subtype.comp
                (MulAut.conjNormal (H := L) t).toMonoidHom) := by
                rw [Subgroup.map_map]
        _ = S_L.map ((MulAut.conj t).toMonoidHom.comp L.subtype) := by rw [hcomp t]
        _ = (S_L.map L.subtype).map (MulAut.conj t).toMonoidHom := by
              rw [Subgroup.map_map]
        _ = S.map (MulAut.conj t).toMonoidHom := by rw [hSLmap]
        _ = S := hSmap t ht
        _ = S_L.map L.subtype := by rw [hSLmap]
    have hP₁fix : ∀ t ∈ T,
        P₁.map (MulAut.conjNormal (H := L) t).toMonoidHom = P₁ := by
      intro t ht
      let φ : MulAut ↥L := MulAut.conjNormal (H := L) t
      have hSLφ : S_L.map φ.toMonoidHom = S_L := hSL_fixed t ht
      have hle : S_L ≤ P₁.map φ.toMonoidHom := by
        rw [← hSLφ]
        exact Subgroup.map_mono hLat.lt₁.le
      rcases hLat.hover (P₁.map φ.toMonoidHom) hle with h | h | h | h
      · have hlt := Subgroup.card_lt_of_lt hLat.lt₁
        rw [← h, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective] at hlt
        exact absurd hlt (lt_irrefl _)
      · exact h
      · have hc : Nat.card P₂ = Nat.card P₁ := by
          rw [← h, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
        omega
      · have htop : P₁ = ⊤ := by
          apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
          rw [h, Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective]
        exact absurd htop hLat.top₁
    have hP₂fix : ∀ t ∈ T,
        P₂.map (MulAut.conjNormal (H := L) t).toMonoidHom = P₂ := by
      intro t ht
      let φ : MulAut ↥L := MulAut.conjNormal (H := L) t
      have hSLφ : S_L.map φ.toMonoidHom = S_L := hSL_fixed t ht
      have hle : S_L ≤ P₂.map φ.toMonoidHom := by
        rw [← hSLφ]
        exact Subgroup.map_mono hLat.lt₂.le
      rcases hLat.hover (P₂.map φ.toMonoidHom) hle with h | h | h | h
      · have hlt := Subgroup.card_lt_of_lt hLat.lt₂
        rw [← h, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective] at hlt
        exact absurd hlt (lt_irrefl _)
      · have hc : Nat.card P₁ = Nat.card P₂ := by
          rw [← h, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
        omega
      · exact h
      · have htop : P₂ = ⊤ := by
          apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
          rw [h, Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective]
        exact absurd htop hLat.top₂
    let X₁ : Subgroup Q := P₁.map L.subtype
    let X₂ : Subgroup Q := P₂.map L.subtype
    have hX₁norm : T ≤ Subgroup.normalizer (X₁ : Set Q) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      let φ : MulAut ↥L := MulAut.conjNormal (H := L) t
      calc
        X₁.map (MulAut.conj t).toMonoidHom
            = P₁.map ((MulAut.conj t).toMonoidHom.comp L.subtype) := by
                simp only [X₁]
                rw [Subgroup.map_map]
        _ = P₁.map (L.subtype.comp φ.toMonoidHom) := by rw [hcomp t]
        _ = (P₁.map φ.toMonoidHom).map L.subtype :=
          (Subgroup.map_map P₁ L.subtype φ.toMonoidHom).symm
        _ = P₁.map L.subtype := by rw [hP₁fix t ht]
        _ = X₁ := rfl
    have hX₂norm : T ≤ Subgroup.normalizer (X₂ : Set Q) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      let φ : MulAut ↥L := MulAut.conjNormal (H := L) t
      calc
        X₂.map (MulAut.conj t).toMonoidHom
            = P₂.map ((MulAut.conj t).toMonoidHom.comp L.subtype) := by
                simp only [X₂]
                rw [Subgroup.map_map]
        _ = P₂.map (L.subtype.comp φ.toMonoidHom) := by rw [hcomp t]
        _ = (P₂.map φ.toMonoidHom).map L.subtype :=
          (Subgroup.map_map P₂ L.subtype φ.toMonoidHom).symm
        _ = P₂.map L.subtype := by rw [hP₂fix t ht]
        _ = X₂ := rfl
    have hX₁le : X₁ ≤ L := Subgroup.map_subtype_le _
    have hX₂le : X₂ ≤ L := Subgroup.map_subtype_le _
    have hX₁ne_bot : X₁ ≠ ⊥ := by
      intro hbot
      have hbot' : P₁.map L.subtype = ⊥ := hbot
      have hP : P₁ = ⊥ := by
        apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
        rw [hbot', Subgroup.map_bot]
      exact (bot_lt_iff_ne_bot.mp (bot_le.trans_lt hLat.lt₁)) hP
    have hX₂ne_bot : X₂ ≠ ⊥ := by
      intro hbot
      have hbot' : P₂.map L.subtype = ⊥ := hbot
      have hP : P₂ = ⊥ := by
        apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
        rw [hbot', Subgroup.map_bot]
      exact (bot_lt_iff_ne_bot.mp (bot_le.trans_lt hLat.lt₂)) hP
    have hX₁ne_L : X₁ ≠ L := by
      intro hXL
      have hXL' : P₁.map L.subtype = L := hXL
      have hP : P₁ = ⊤ := by
        apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
        rw [hXL', Subgroup.map_top, Subgroup.range_subtype]
      exact hLat.top₁ hP
    have hX₂ne_L : X₂ ≠ L := by
      intro hXL
      have hXL' : P₂.map L.subtype = L := hXL
      have hP : P₂ = ⊤ := by
        apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
        rw [hXL', Subgroup.map_top, Subgroup.range_subtype]
      exact hLat.top₂ hP
    have hsup : X₁ ⊔ X₂ = L := by
      have htop : P₁ ⊔ P₂ = ⊤ := hLat.toTwoPar.sup_eq_top
      calc
        X₁ ⊔ X₂ = P₁.map L.subtype ⊔ P₂.map L.subtype := rfl
        _ = (P₁ ⊔ P₂).map L.subtype := (Subgroup.map_sup P₁ P₂ L.subtype).symm
        _ = (⊤ : Subgroup ↥L).map L.subtype :=
          congrArg (Subgroup.map L.subtype) htop
        _ = L := by
          rw [Subgroup.map_top]
          exact Subgroup.range_subtype L
    have hS_ne_bot : S ≠ ⊥ := by
      intro hbot
      have hS_L_bot : S_L = ⊥ := by
        have := congrArg (fun X : Subgroup Q => X.subgroupOf L) hbot
        simpa [S_L] using this
      rw [hS_L_bot, Subgroup.card_bot] at hS_card
      omega
    exact false_of_invariant_pair hLn hLs hnab hT hS_ne_bot hMt hMax
      hX₁le hX₂le hX₁ne_bot hX₂ne_bot hX₁ne_L hX₂ne_L hX₁norm hX₂norm hsup

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

