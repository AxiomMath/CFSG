module

public section

namespace CFSG.KS.SporSch

@[expose] def hnStrongText : String := include_str "hnstrong.txt"

@[expose] def hnStrongRows : Array (Array (Array Nat)) :=
  let b := hnStrongText.toUTF8
  Array.ofFn (n := 34) fun t => Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j =>
    (b[(t.val * 133 + i.val) * 134 + j.val]!.toNat - 48) % 5

end CFSG.KS.SporSch

end
