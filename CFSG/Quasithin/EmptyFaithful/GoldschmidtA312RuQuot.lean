module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuY2Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import Certificates.Certificate4163

public section

namespace CFSG.Quasithin.A312Ru

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert CFSG.QuasithinUnique.Ch1.SporLat.Ru
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_oddGen_cert :
    OddGenOK ruData.n ruQuotL2 ruQuot2 ruQuot2Words :=
  Certificates.certificate4163

section Quot

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem quot_card_le_one_of_oddGen (C : LatCtx Γ n Lab) {j : ℕ} (hj : j < C.J) (B : List ℕ)
    (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    (xs : List QuotGen) (ws : List (List ℕ))
    (hQ : OddGenOK n (C.D.sTabs ++ C.D.mt[j]!) xs ws)
    (N : Subgroup (C.Y j)) [N.Normal] (hp : IsPGroup 2 (C.Y j ⧸ N)) :
    Nat.card (C.Y j ⧸ N) ≤ 1 := by
  classical
  obtain ⟨hxs, hlen, hwl, hws⟩ := hQ
  have hL : C.D.sTabs ++ C.D.mt[j]! = genTabs n (C.sg ++ C.gens j) := (C.Y_letters hj).symm
  generalize hLL : C.D.sTabs ++ C.D.mt[j]! = L at hL hxs hlen hws
  generalize hEE : C.sg ++ C.gens j = E at hL
  have hLlen : L.length = E.length := by rw [hL, genTabs_length]
  have hel : ∀ l < E.toArray.size, L.toArray.getD l #[] = (tab n (E.toArray.getD l 1)).toArray := by
    rw [hL]; exact genTabs_hel E
  have hwE : ∀ x ∈ xs, ∀ l ∈ x.w, l < E.toArray.size := fun x hx l hl => by
    have := (hxs x hx).1 l hl
    simpa [hLlen] using this
  obtain ⟨gx, hgx⟩ : ∃ gx : QuotGen → Γ, ∀ x, gx x = (evalElt E.toArray x.w) ^ x.k :=
    ⟨_, fun _ => rfl⟩
  have hGtx : ∀ x ∈ xs, quotGt n L x = (tab n (gx x)).toArray := by
    intro x hx
    unfold quotGt
    rw [hgx, tab_pow, wordTabA_eq E.toArray L.toArray hel x.w (hwE x hx)]
  have hid : ∀ b ∈ B, img (idTab n) b = b := by
    intro b hb
    have hbn := hB b hb
    simp [img, idTab, Array.getD_eq_getD_getElem?, hbn]
  have hgm : ∀ x ∈ xs, (gx x) ^ x.m = 1 := by
    intro x hx
    apply hbase
    intro b hb
    have h1 := (hxs x hx).2.2
    rw [hGtx x hx, ← tab_pow] at h1
    rw [← img_tab, h1]
    exact hid b hb
  have hGi : ∀ x ∈ xs, quotGi n L x = (tab n (gx x)⁻¹).toArray := by
    intro x hx
    unfold quotGi
    rw [hGtx x hx, ← tab_pow]
    congr 2
    have hm1 : 1 ≤ x.m := by have := (hxs x hx).2.1; omega
    have h2 : gx x * (gx x) ^ (x.m - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hm1]; exact hgm x hx
    exact eq_inv_of_mul_eq_one_right h2
  have hYE : C.Y j = Subgroup.closure {x | x ∈ E} := by
    unfold LatCtx.Y; rw [hEE]
  have hels : ∀ l < E.toArray.size, E.toArray.getD l 1 ∈ C.Y j := by
    intro l hl
    have := evalElt_getD_mem_closure E.toArray hl
    rw [LatCtx.toList_toArray_set] at this
    rwa [hYE]
  have hYmem : ∀ x ∈ xs, gx x ∈ C.Y j := by
    intro x hx
    rw [hgx]
    exact Subgroup.pow_mem _ (evalElt_mem E.toArray hels x.w (hwE x hx)) _
  let Nγ : Subgroup Γ := N.map (C.Y j).subtype
  have hNmem : ∀ x ∈ xs, gx x ∈ Nγ := by
    intro x hx
    refine ⟨⟨gx x, hYmem x hx⟩, ?_, rfl⟩
    refine mem_of_pow_eq_one_odd N hp (hxs x hx).2.1 ?_
    apply Subtype.ext
    simpa using hgm x hx
  let gl : List Γ := xs.map gx ++ xs.map (fun x => (gx x)⁻¹)
  have hglmem : ∀ g ∈ gl, g ∈ Nγ := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
      exact hNmem x hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
      exact Nγ.inv_mem (hNmem x hx)
  have hT : xs.map (quotGt n L) ++ xs.map (quotGi n L) = genTabs n gl := by
    simp only [gl]
    rw [genTabs_append]
    simp only [genTabs, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro x hx
      simp [Function.comp, hGtx x hx]
    · apply List.map_congr_left
      intro x hx
      simp [Function.comp, hGi x hx]
  have hgl : ∀ l < gl.toArray.size, gl.toArray.getD l 1 ∈ Nγ := by
    intro l hl
    refine (Subgroup.closure_le Nγ).mpr ?_ (evalElt_getD_mem_closure gl.toArray hl)
    rw [LatCtx.toList_toArray_set]
    exact hglmem
  have hglsz : gl.toArray.size = 2 * xs.length := by simp [gl]; omega
  have hletter : ∀ e ∈ E, e ∈ Nγ := by
    intro e he
    obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem he
    have hjw : j' < ws.length := by omega
    have hjL : j' < L.length := by omega
    have hmemw : ws[j']! ∈ ws := by rw [getElem!_pos ws j' hjw]; exact List.getElem_mem hjw
    have hwlt : ∀ l ∈ ws[j']!, l < gl.toArray.size := fun l hl => by
      rw [hglsz]; exact hwl _ hmemw l hl
    have h1 := hws j' hjL
    rw [hT, wordTabA_eq gl.toArray (genTabs n gl).toArray (genTabs_hel gl) _ hwlt] at h1
    have h2 : L[j']! = (tab n (E.toArray.getD j' 1)).toArray := by
      have h := hel j' (by simpa using hj')
      rw [getElem!_pos L j' hjL]
      simpa [Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem hjL] using h
    rw [h2] at h1
    have h3 : evalElt gl.toArray ws[j']! = E.toArray.getD j' 1 := by
      apply eq_of_act_eq_base hB hbase
      intro b hb
      rw [← img_tab, ← img_tab, h1]
    have h4 : E[j'] = E.toArray.getD j' 1 := by
      simp [Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem hj']
    rw [h4, ← h3]
    exact evalElt_mem gl.toArray hgl _ hwlt
  have hYN : C.Y j ≤ Nγ := by
    rw [hYE, Subgroup.closure_le]
    exact hletter
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, hzy⟩ := hYN y.2
    have : z = y := Subtype.ext hzy
    rwa [← this]
  rw [hNtop]
  simp

end Quot

theorem ru_quotL2 :
    ruCtx.D.sTabs ++ ruCtx.D.mt[2]! = ruQuotL2 :=
  ru_letters2

theorem ru_Y2_quot
    (N : Subgroup (ruCtx.Y 2)) [N.Normal] (hp : IsPGroup 2 (ruCtx.Y 2 ⧸ N)) :
    Nat.card (ruCtx.Y 2 ⧸ N) ≤ 1 := by
  have hj : 2 < ruCtx.J := by rw [ru_J]; norm_num
  refine quot_card_le_one_of_oddGen ruCtx hj ruB (base_lt ru_facts) (base_property ru_facts)
    ruQuot2 ruQuot2Words ?_ N hp
  rw [ru_quotL2]
  exact ru_oddGen_cert

end CFSG.Quasithin.A312Ru
