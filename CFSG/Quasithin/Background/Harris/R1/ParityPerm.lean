module

public import CFSG.Quasithin.Background.Harris.R1.PermHom

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

open Equiv in
theorem sign_eq_one_of_pairs : ∀ σ : Perm (Fin 5), σ 0 = 0 →
    (∀ i j : Fin 5, i ≠ 0 → j ≠ 0 → i ≠ j →
      (∀ m, Even ([σ i, σ j].countP (fun x => decide (x ≠ m)) +
        [i, j].countP (fun x => decide (x ≠ m)))) ∨
      (∀ m, Even ([σ i, σ j].countP (fun x => decide (x ≠ m)) +
        [0, i, j].countP (fun x => decide (x ≠ m))))) →
    Perm.sign σ = 1 := by
  decide +kernel

theorem countP_map_equiv {Ω : Type} [DecidableEq Ω] (E : Ω ≃ Fin 5) (l : List Ω) (m : Ω) :
    (l.map E).countP (fun x => decide (x ≠ E m)) = l.countP (fun x => decide (x ≠ m)) := by
  rw [List.countP_map]
  congr 1
  funext x
  simp [E.injective.eq_iff]


namespace FamCtxLemmas

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω)

include C

theorem conj_zf_of_mem_sup {b : G} (hb : b ∈ K1 ⊔ S) (i : Ω) :
    ∃ ε ∈ Zs, b * C.zf i * b⁻¹ = C.zf (permHom C ⟨b, hb⟩ i) * ε := by
  set m : G := b * C.zf i * b⁻¹ with hm
  have hmV : m ∈ C.D.Vf (conjClosure Zs L2) (permHom C ⟨b, hb⟩ i) := by
    have h1 : m ∈ conjSub b (C.D.Vf (conjClosure Zs L2) i) := mul_mem_conjSub (C.zf_mem i)
    rwa [conjSub_permHom C ⟨b, hb⟩ i] at h1
  have hmZ : m ∉ Zs := by
    intro hmZ
    apply C.zf_not_mem i
    have hk : b ∈ Subgroup.centralizer (Zs : Set G) := C.sup_le_centralizer_Zs hb
    have hcomm : m * b = b * m := Subgroup.mem_centralizer_iff.mp hk m hmZ
    have e : C.zf i = m := by
      calc C.zf i = b⁻¹ * (b * C.zf i * b⁻¹) * b := by group
        _ = b⁻¹ * (m * b) := by rw [hm]; group
        _ = b⁻¹ * (b * m) := by rw [hcomm]
        _ = m := by group
    rw [e]
    exact hmZ
  rcases C.Vf_eq hmV with h1 | h1
  · exact absurd h1 hmZ
  · exact ⟨_, h1, by group⟩


variable [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] [DecidableEq Ω] in
theorem coe_gprod_two (a c : Ω) :
    ((gprod C.wU [a, c] : ↥(vBeta K1 L2 S Zs)) : G) = C.zf a * C.zf c := by
  simp [gprod, FamCtx.wU]

omit [Fintype Ω] [DecidableEq Ω] in
theorem coe_gprod_three (p a c : Ω) :
    ((gprod C.wU [p, a, c] : ↥(vBeta K1 L2 S Zs)) : G) = C.zf p * (C.zf a * C.zf c) := by
  simp [gprod, FamCtx.wU]

theorem pair_parity_split (hΩ : 2 ≤ Fintype.card Ω) {b : G} (hb : b ∈ K1 ⊔ S) (i j : Ω) :
    (b * (C.zf i * C.zf j) * b⁻¹ * (C.zf i * C.zf j)⁻¹ ∈ Zs →
      ∀ m, Even ([permHom C ⟨b, hb⟩ i, permHom C ⟨b, hb⟩ j].countP (fun x => decide (x ≠ m)) +
        [i, j].countP (fun x => decide (x ≠ m)))) ∧
    ((C.zf C.D.pt)⁻¹ * (b * (C.zf i * C.zf j) * b⁻¹ * (C.zf i * C.zf j)⁻¹) ∈ Zs →
      ∀ m, Even ([permHom C ⟨b, hb⟩ i, permHom C ⟨b, hb⟩ j].countP (fun x => decide (x ≠ m)) +
        [C.D.pt, i, j].countP (fun x => decide (x ≠ m)))) := by
  obtain ⟨i₀, j₀, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Ω)
  have hG := C.gramRel hij
  have hz : C.zU i₀ j₀ ≠ 1 := fun h => C.cm_ne_one hij (congrArg Subtype.val h)
  set σ := permHom C ⟨b, hb⟩ with hσ
  obtain ⟨εi, hεi, hi⟩ := conj_zf_of_mem_sup C hb i
  obtain ⟨εj, hεj, hj⟩ := conj_zf_of_mem_sup C hb j
  have hcz : ∀ u ∈ vBeta K1 L2 S Zs, ∀ e ∈ Zs, e * u = u * e :=
    fun u hu e he => (C.Zs_central hu he).symm
  have hbab : b * (C.zf i * C.zf j) * b⁻¹ = C.zf (σ i) * εi * (C.zf (σ j) * εj) := by
    rw [show b * (C.zf i * C.zf j) * b⁻¹ = (b * C.zf i * b⁻¹) * (b * C.zf j * b⁻¹) by group,
      hi, hj]
  generalize hvdef : b * (C.zf i * C.zf j) * b⁻¹ * (C.zf i * C.zf j)⁻¹ = v
  have hvb : b * (C.zf i * C.zf j) * b⁻¹ = v * (C.zf i * C.zf j) := by
    rw [← hvdef]; group
  have hZP : ∀ e (he : e ∈ Zs), ∀ g : ↥(vBeta K1 L2 S Zs),
      (⟨e, F112J2.Zs_le_vBeta K1 L2 S Zs he⟩ : ↥(vBeta K1 L2 S Zs)) * g =
        g * ⟨e, F112J2.Zs_le_vBeta K1 L2 S Zs he⟩ :=
    fun e he g => Subtype.ext (C.Zs_central g.2 he).symm
  have hεij : εi * εj ∈ Zs := Zs.mul_mem hεi hεj
  have hLHS : C.zf (σ i) * C.zf (σ j) * (εi * εj) =
      b * (C.zf i * C.zf j) * b⁻¹ := by
    rw [hbab]
    calc C.zf (σ i) * C.zf (σ j) * (εi * εj)
        = C.zf (σ i) * (C.zf (σ j) * εi) * εj := by simp only [mul_assoc]
      _ = C.zf (σ i) * (εi * C.zf (σ j)) * εj := by rw [← hcz _ (C.zf_mem_U (σ j)) εi hεi]
      _ = _ := by simp only [mul_assoc]
  refine ⟨fun hvZ => ?_, fun hvZ => ?_⟩
  · have heq : gprod C.wU [σ i, σ j] * ⟨εi * εj, F112J2.Zs_le_vBeta K1 L2 S Zs hεij⟩ =
        gprod C.wU [i, j] * ⟨v, F112J2.Zs_le_vBeta K1 L2 S Zs hvZ⟩ := by
      apply Subtype.ext
      show ((gprod C.wU [σ i, σ j] : ↥(vBeta K1 L2 S Zs)) : G) * (εi * εj) =
        ((gprod C.wU [i, j] : ↥(vBeta K1 L2 S Zs)) : G) * v
      rw [coe_gprod_two, coe_gprod_two, hLHS, hvb]
      have := hcz (C.zf i) (C.zf_mem_U i) v hvZ
      have h2 := hcz (C.zf j) (C.zf_mem_U j) v hvZ
      calc v * (C.zf i * C.zf j) = (v * C.zf i) * C.zf j := by rw [mul_assoc]
        _ = (C.zf i * v) * C.zf j := by rw [this]
        _ = C.zf i * (v * C.zf j) := by rw [mul_assoc]
        _ = C.zf i * (C.zf j * v) := by rw [h2]
        _ = _ := by rw [mul_assoc]
    exact fun m => hG.even_countP_of_eq hz (hZP _ hεij) (hZP _ hvZ) heq m
  · set ε := (C.zf C.D.pt)⁻¹ * v with hε
    have hvε : v = C.zf C.D.pt * ε := by rw [hε]; group
    have heq : gprod C.wU [σ i, σ j] * ⟨εi * εj, F112J2.Zs_le_vBeta K1 L2 S Zs hεij⟩ =
        gprod C.wU [C.D.pt, i, j] * ⟨ε, F112J2.Zs_le_vBeta K1 L2 S Zs hvZ⟩ := by
      apply Subtype.ext
      show ((gprod C.wU [σ i, σ j] : ↥(vBeta K1 L2 S Zs)) : G) * (εi * εj) =
        ((gprod C.wU [C.D.pt, i, j] : ↥(vBeta K1 L2 S Zs)) : G) * ε
      rw [coe_gprod_two, coe_gprod_three, hLHS, hvb, hvε]
      have h1 := hcz (C.zf i) (C.zf_mem_U i) ε hvZ
      have h2 := hcz (C.zf j) (C.zf_mem_U j) ε hvZ
      calc C.zf C.D.pt * ε * (C.zf i * C.zf j)
          = C.zf C.D.pt * ((ε * C.zf i) * C.zf j) := by simp only [mul_assoc]
        _ = C.zf C.D.pt * ((C.zf i * ε) * C.zf j) := by rw [h1]
        _ = C.zf C.D.pt * (C.zf i * (ε * C.zf j)) := by simp only [mul_assoc]
        _ = C.zf C.D.pt * (C.zf i * (C.zf j * ε)) := by rw [h2]
        _ = _ := by simp only [mul_assoc]
    exact fun m => hG.even_countP_of_eq hz (hZP _ hεij) (hZP _ hvZ) heq m


theorem pair_parity (hΩ : 2 ≤ Fintype.card Ω) {b : G} (hb : b ∈ K1 ⊔ S) (i j : Ω)
    (hv : b * (C.zf i * C.zf j) * b⁻¹ * (C.zf i * C.zf j)⁻¹ ∈ C.D.Vf (conjClosure Zs L2) C.D.pt) :
    (∀ m, Even ([permHom C ⟨b, hb⟩ i, permHom C ⟨b, hb⟩ j].countP (fun x => decide (x ≠ m)) +
        [i, j].countP (fun x => decide (x ≠ m)))) ∨
      (∀ m, Even ([permHom C ⟨b, hb⟩ i, permHom C ⟨b, hb⟩ j].countP (fun x => decide (x ≠ m)) +
        [C.D.pt, i, j].countP (fun x => decide (x ≠ m)))) := by
  have h := pair_parity_split C hΩ hb i j
  rcases C.Vf_eq hv with hvZ | hvZ
  · exact Or.inl (h.1 hvZ)
  · exact Or.inr (h.2 hvZ)

theorem sign_permHom_eq_one (hΩ : Fintype.card Ω = 5) {b : G} (hb : b ∈ K1 ⊔ S)
    (hbV : ∀ v ∈ C.D.Vf (conjClosure Zs L2) C.D.pt, v * b = b * v)
    (hcom : ∀ i j : Ω, i ≠ C.D.pt → j ≠ C.D.pt → i ≠ j →
      b * (C.zf i * C.zf j) * b⁻¹ * (C.zf i * C.zf j)⁻¹ ∈ C.D.Vf (conjClosure Zs L2) C.D.pt) :
    Equiv.Perm.sign (permHom C ⟨b, hb⟩) = 1 := by
  set σ := permHom C ⟨b, hb⟩ with hσ
  set pt := C.D.pt with hpt
  have hσpt : σ pt = pt := by
    have hnorm : b ∈ Subgroup.normalizer (C.D.Vf (conjClosure Zs L2) pt : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hbV)
    exact permOf_eq_of_conjSub C (conjSub_eq_of_mem_normalizer hnorm)
  let e0 : Ω ≃ Fin 5 := (Fintype.equivFin Ω).trans (finCongr hΩ)
  let E : Ω ≃ Fin 5 := e0.trans (Equiv.swap (e0 pt) 0)
  have hE : E pt = 0 := by simp [E]
  have hs : ∀ x, (E.permCongr σ) (E x) = E (σ x) := fun x => by simp [Equiv.permCongr_apply]
  have h := sign_eq_one_of_pairs (E.permCongr σ) (by
    have := hs pt
    rw [hE, hσpt, hE] at this
    exact this) (by
    intro i' j' hi' hj' hij'
    obtain ⟨i, rfl⟩ := E.surjective i'
    obtain ⟨j, rfl⟩ := E.surjective j'
    have hi : i ≠ pt := fun h => hi' (h ▸ hE)
    have hj : j ≠ pt := fun h => hj' (h ▸ hE)
    have hij : i ≠ j := fun h => hij' (h ▸ rfl)
    simp only [hs]
    rcases pair_parity C (by omega) hb i j (hcom i j hi hj hij) with h | h
    · left
      intro m'
      obtain ⟨m, rfl⟩ := E.surjective m'
      have := h m
      rw [← countP_map_equiv E [σ i, σ j] m, ← countP_map_equiv E [i, j] m] at this
      simpa using this
    · right
      intro m'
      obtain ⟨m, rfl⟩ := E.surjective m'
      have := h m
      rw [← countP_map_equiv E [σ i, σ j] m, ← countP_map_equiv E [pt, i, j] m] at this
      simpa [hE] using this)
  rwa [Equiv.Perm.sign_permCongr] at h

end FamCtxLemmas

end CFSG.Quasithin.Background.Harris.R1
